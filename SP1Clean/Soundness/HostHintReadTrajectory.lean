import SP1Clean.Soundness.HostHintReadGrounding
import SP1Clean.Soundness.CoreExecutionTrajectory
import SP1Clean.Soundness.HostQueueCurrent

/-! # Hint dispatch on the complete carrier's Sail/host replay

The same CPU order drives memory grounding and host queue history. Incoming State truth recovers
the actual replayed prefix, while the authenticated ECALL fetch excludes a stopped host. HINT_LEN
then observes that host's queue, and HINT_READ consumes it using the engine's original register
currency. No preceding-replay or running-host premise is supplied to these dispatch theorems.
Complete step/frame facts and outgoing snapshot agreement remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {channels : List (RawChannel (ZMod p))}

private theorem source_ordering
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    LocalCore.OrderingChannels (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) :=
  HostLocalCore.orderingChannels (HostHintQueueBoundary.expanded witness)
    (auxiliaryInterface (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints)))
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced)

private theorem source_data
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data = witness.data := rfl

private theorem source_public
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).publicInput = witness.publicInput := rfl

/-- The complete carrier's timeline agrees with semantic event time at every index. -/
theorem GroundingCarrier.timeline_events
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    carrier.timeline = eventTimeline carrier.events source.clock := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.expanded_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  have encoding := LocalCore.source_state_encoding_of_byte _ checked ordering.byte
  rw [source_public] at encoding
  apply ExecutionCarrier.timeline_eq_events carrier source.clock encoding.1
  intro event member
  have duration := (LocalCore.executionRows_advancing_of_orderingChannels _ checked ordering member).2
  rw [source_data, ExecutionRow.edge_eq_facts] at duration
  exact duration

/-- Replay starts at the complete local source and threads the selected native host policy. -/
noncomputable def GroundingCarrier.pairedTrajectory (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness) : ℕ → Option ExecutionState :=
  ExecutionCarrier.pairedTrajectory carrier ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) source.realize

noncomputable def GroundingCarrier.trajectory (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness) : Trajectory :=
  fun n => (carrier.pairedTrajectory valid n).map ExecutionState.sail

theorem GroundingCarrier.trajectory_zero (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness) :
    carrier.trajectory valid 0 = some source.sail.realize := rfl

private theorem source_running
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p}
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) :
    source.host.exitCode = none := by
  by_contra stopped
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.expanded_constraints witness constraints)
  have ordering := source_ordering witness constraints balanced
  have contract := LocalCore.public_contract_of_byte _ checked (ordering.byte _ (HostLocalCore.localWitness
    (HostHintQueueBoundary.expanded witness)).mem_allTables_verifierTable)
  rw [source_public] at contract
  have same := contract.2.2.2 stopped
  have clock : StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) =
      StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) := by
    change clkNat witness.publicInput.final_clk_high witness.publicInput.final_clk_low =
      clkNat witness.publicInput.init_clk_high witness.publicInput.init_clk_low
    rw [same.1, same.2]
  have nonempty : 0 < carrier.rows.length := by
    have count := carrier.aligned.length_eq
    have positive := List.length_pos_of_mem (carrier.exhaustive.mem_iff.mpr member)
    simp only [List.length_map] at count
    omega
  have strict := Timeline.start_lt_of_lt carrier.timeline nonempty
  rw [carrier.timeline_start, carrier.finalClock, clock] at strict
  exact (lt_irrefl _ strict)

private theorem prefix_of_state (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p}
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull) :
    ∃ n current, carrier.ordered[n]? = some event ∧
      carrier.ordered = carrier.ordered.take n ++ event :: carrier.ordered.drop (n + 1) ∧
      carrier.pairedTrajectory valid n = some current ∧
      replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) source.realize
        ((carrier.ordered.take n).map ExecutionRow.event) = some current ∧
      current.sail.regs.get? LeanRV64D.Defs.Register.PC = some (StateMsg.pcBits (event.facts witness.data).statePull) := by
  obtain ⟨n, state, present, time, pc, _⟩ := pull
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  obtain ⟨current, paired, sail⟩ := Option.map_eq_some_iff.mp present
  have atIndex := ExecutionCarrier.ordered_at carrier member time
  obtain ⟨bound, atEvent⟩ := List.getElem?_eq_some_iff.mp atIndex
  refine ⟨n, current, List.getElem?_eq_some_iff.mpr ⟨bound, atEvent⟩, ?_, paired, ?_, ?_⟩
  · rw [← atEvent, List.getElem_cons_drop, List.take_append_drop]
  · simpa only [GroundingCarrier.pairedTrajectory, ExecutionCarrier.pairedTrajectory, executionTrajectory,
      ExecutionCarrier.events, List.map_take] using paired
  · rwa [sail]

/-- Incoming State truth locates the physical HINT_LEN at its actual replayed host prefix.
The circuit's result is the length observed there, without assuming earlier replay separately. -/
theorem GroundingCarrier.hintLength_result (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (empty : Bool) (env : Environment (ZMod p))
    (handler : (some empty, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.expanded witness)))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (some empty, env))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull) :
    ∃ n current, carrier.ordered[n]? = some event ∧ carrier.pairedTrajectory valid n = some current ∧
      Word.toBitVec64 (valueFromOffset HostHintLengthChip.Inputs 0 env).call.result = current.host.io.hintLength := by
  obtain ⟨n, current, atIndex, split, paired, replayed, _⟩ := prefix_of_state valid carrier member pull
  exact ⟨n, current, atIndex, paired, HostQueueCurrent.length_of_source_prefix witness constraints balanced
    carrier.exhaustive carrier.cpuWalk (carrier.ordered.take n) (carrier.ordered.drop (n + 1)) event split
    empty env handler clock _ _ current replayed⟩

private theorem read_member {resources : List (Component (ZMod p))}
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment) :
    (none, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices (queueTables witness) := by
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp member
  simp only [TransitionView.readIndexedRows, HostQueueOrder.indices, queueTables,
    List.zip_cons_cons, List.flatMap_cons]
  exact List.mem_append_left _ (List.mem_map_of_mem physicalMem)

/-- HINT_READ dispatch and its exact padded writes follow at the replayed prefix from incoming
State truth and operand currency. Running status and previous replay are derived internally. -/
theorem GroundingCarrier.hintRead_run (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.expanded witness)).table.map
      (handlerTable (HostHintQueueBoundary.expanded witness)).environment)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (currency : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event).memPulls,
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ n current store bytes remaining, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧
      HintQueue.Extends store (HintQueue.ofList source.host.io.hints).1 ∧
      current.host.io.hints = bytes :: remaining ∧
      (HostHintReadCoverage.input env).next.Binds store remaining ∧
      current.host.run ⟨{ readOnly := image.readOnly }, p⟩ (.ofSail current.sail) =
        some (HostHintReadChip.execution (HostHintReadCoverage.input env) current.host bytes remaining) ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env)
          (wordTables (HostHintQueueBoundary.expanded witness)))).map HintReadWrites.produced).Perm
        (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes) := by
  obtain ⟨n, current, atIndex, split, paired, replayed, pc⟩ := prefix_of_state valid carrier member pull
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final)
    (source_interface (p := p) source.host.io.hints)
  obtain ⟨physical, active, _, sameEvent⟩ := HostQueueCPUOrder.call_cpu_at (HostHintQueueBoundary.expanded witness)
    interface checks balance (none, env) (read_member _ env handler) event member clock
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.expanded witness)
    (source_program_silent source final) checks balance physical active
  have fetch := (committed.ecall_of_opcode rfl).1
  rw [sameEvent] at pc
  have running := replayEvents?_running_of_fetch (source_running carrier constraints balanced member) replayed pc fetch
  have original : ∀ mp ∈ (event.facts witness.data).memPulls,
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value :=
    fun mp present => currency mp (List.mem_append_left _ present)
  rw [carrier.timeline_events constraints balanced] at original
  obtain ⟨store, bytes, remaining, extension, hints, next, executed, writes⟩ :=
    HostQueueCurrent.run_of_source_prefix valid witness constraints balanced carrier.exhaustive carrier.cpuWalk
      (carrier.ordered.take n) (carrier.ordered.drop (n + 1)) event split env handler clock current replayed running original
  exact ⟨n, current, store, bytes, remaining, atIndex, paired, extension, hints, next, executed, writes⟩

end SP1Clean.Soundness.HostHintReadCPU
