import SP1Clean.Soundness.HostQueueCPUReplay
import SP1Clean.Soundness.HostLocalCoreProgram
import SP1Clean.Soundness.HostHintReadLocalMemory

/-! # Current host hints derived from installed queue history

Before an actual HINT_LEN/HINT_READ CPU event, successful replay of the preceding CPU prefix
determines the current host queue. The installed queue AIR binds that same queue to its current
frontier. No independent current-head or byte-content premise is supplied by the caller.
Memory currency and execution of the current call remain the mixed grounding obligations.
-/

namespace SP1Clean.Soundness.HostQueueCurrent

open Circuit Air.Flat Model.Core HostHintReadLocal HostQueueOrder HostQueueCPUOrder HostQueueCPUReplay
open NativeCore Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem filter_projection {Row Label : Type*} (clock : Row → ℕ)
    (project : Row → Option (ℕ × Label)) (rows : List Row) (keys : List ℕ)
    (time : ∀ row stamp, project row = some stamp → stamp.1 = clock row) :
    (rows.filterMap project).filter (fun stamp => decide (stamp.1 ∈ keys)) =
      (rows.filter (fun row => decide (clock row ∈ keys))).filterMap project := by
  rw [List.filter_filterMap, List.filterMap_filter]
  apply List.filterMap_congr
  intro row _
  cases found : project row with
  | none => simp
  | some stamp => simp [time row stamp found, Option.filter]

private theorem erase_projection {Row Label : Type*} (clock : Row → ℕ)
    (event : Row → Option Label) (rows : List Row) :
    (rows.filterMap (fun row => (event row).map fun label => (clock row, label))).map Prod.snd =
      rows.filterMap event := by
  simp only [List.map_filterMap, Option.map_map, Function.comp_def, Option.map_id_fun', id_eq]

private theorem prefix_projection (data : ProverData (ZMod p))
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (path : List (Row (p := p)))
    (sorted : ((prior ++ event :: rest).map fun row => StateMsg.timeNat (row.edge data).1).Pairwise (· < ·))
    (projected : (prior ++ event :: rest).filterMap (stampedCPU data) =
      path.map fun row => (eventTime row, HostQueueHistory.event row)) :
    (prior.map ExecutionRow.event).filterMap queueEvent? =
      (beforeCPU data prior path).map HostQueueHistory.event := by
  let time := fun row : ExecutionRow p => StateMsg.timeNat (row.edge data).1
  have kept : (prior ++ event :: rest).filter (fun row => decide (time row ∈ prior.map time)) = prior := by
    rw [List.filter_mem_prefix_eq_filter_lt time time (prior ++ event :: rest)
      (List.pairwise_map.mp sorted) (fun _ member => member)]
    exact List.filter_lt_eq_prefix time (List.pairwise_map.mp sorted)
  have selected := congrArg (List.filter (fun stamp : ℕ × HintQueue.Event => decide (stamp.1 ∈ prior.map time))) projected
  rw [filter_projection time (stampedCPU data) _ _ (fun row stamp found => by
    obtain ⟨label, _, rfl⟩ := Option.map_eq_some_iff.mp found
    rfl), kept, List.filter_map] at selected
  have erased := congrArg (List.map Prod.snd) selected
  rw [show prior.filterMap (stampedCPU data) =
    prior.filterMap (fun row => (queueEvent? row.event).map fun label => (time row, label)) from rfl,
    erase_projection] at erased
  simpa only [List.filterMap_map, List.map_map, Function.comp_def, beforeCPU] using erased

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

/-- The current queue is derived at a replayed CPU prefix. Only that preceding prefix must have
executed; the current call's success is not assumed. The full host state supplies the bytes. -/
theorem of_prefix
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (specs : ∀ table ∈ queueTables witness, table.Spec)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    {path : List (Row (p := p))} {initial final : HostHintQueue.State (ZMod p)} {upper : HintQueue.Store}
    (queueExhaustive : path.Perm (TransitionView.readIndexedRows indices (queueTables witness)))
    (queueWalk : Walk.IsWalk edge initial final path)
    (history : HostHintQueueHistory.History source.host.io.hints final upper path)
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (split : cpu = prior ++ event :: rest)
    (row : Row (p := p)) (member : row ∈ path)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = eventTime row)
    (policy : HostPolicy) (program : Target.GuestProgram) (current : ExecutionState)
    (replayed : replayEvents? policy program source.realize (prior.map ExecutionRow.event) = some current) :
    ∃ store, HintQueue.Extends store upper ∧ (edge row).1.Binds store current.host.io.hints := by
  have sorted := LocalCore.ordered_times_pairwise (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints)
    (HostLocalCore.orderingChannels witness (auxiliaryInterface interface) constraints balanced) cpuExhaustive cpuWalk
  have projection := cpu_projection witness interface constraints balanced specs cpuExhaustive cpuWalk
    queueExhaustive queueWalk
  have prefixEq := prefix_projection witness.data prior rest event path (split ▸ sorted) (split ▸ projection)
  have safe := cpu_safe witness interface constraints balanced specs
  have actual := replayEvents?_queue (fun label present => by
    obtain ⟨cpuRow, rowMem, rfl⟩ := List.mem_map.mp present
    apply safe cpuRow (cpuExhaustive.mem_iff.mp _)
    rw [split]
    exact List.mem_append_left _ rowMem) replayed
  rw [prefixEq] at actual
  obtain ⟨store, hints, bounded, observed, binding⟩ := current_at_cpu witness.data history
    (times_pairwise queueWalk (fun row member => rows_spec _ (queueTables_aligned witness) specs row
      (queueExhaustive.mem_iff.mp member))) row member (split ▸ sorted)
    (split ▸ clocks_sublist witness interface constraints balanced specs queueExhaustive queueWalk cpuExhaustive cpuWalk) clock
  have equal : hints = current.host.io.hints := Option.some.inj (observed.symm.trans actual)
  exact ⟨store, bounded, equal ▸ binding⟩

/-- In the installed source-record assembly, raw AIR constraints and balance derive the current
queue at any actual queue syscall. There is no current-queue or record-authentication premise. -/
theorem source_current {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (split : cpu = prior ++ event :: rest)
    (row : Row (p := p))
    (member : row ∈ TransitionView.readIndexedRows indices (queueTables (HostHintQueueBoundary.expanded witness)))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = eventTime row)
    (policy : HostPolicy) (program : Target.GuestProgram) (current : ExecutionState)
    (replayed : replayEvents? policy program source.realize (prior.map ExecutionRow.event) = some current) :
    ∃ store, HintQueue.Extends store (HintQueue.ofList source.host.io.hints).1 ∧
      (edge row).1.Binds store current.host.io.hints := by
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final) (bankFinal := bankFinal)
    (source_interface (p := p) source.host.io.hints)
  have specs := queue_specs (HostHintQueueBoundary.expanded witness) interface _
    (HostHintQueueBoundary.source_authentication witness constraints) checks balance
  obtain ⟨path, exhaustive, walk, history⟩ := HostHintQueueHistory.source_history witness constraints balanced
  exact of_prefix (HostHintQueueBoundary.expanded witness) interface checks balance specs
    cpuExhaustive cpuWalk exhaustive walk history prior rest event split row (exhaustive.mem_iff.mpr member)
    clock policy program current replayed

/-- Installed non-word hint resources cannot create positive write permissions. -/
theorem source_permission_pulls (source : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) :
    ∀ component ∈ (HostCallReceivers.available (p := p)).map (·.component) ++
      (sourceResources source.host.io.hints ++ [⟨(HostHintQueueBoundary.boundary source final bankFinal).circuit⟩]),
      WritePermission.Pulls component := by
  intro component member
  rcases List.mem_append.mp member with handler | resource
  · exact available_permission_pulls component handler
  · have checked : (sourceResources (p := p) source.host.io.hints ++
        [(⟨(HostHintQueueBoundary.boundary source final bankFinal).circuit⟩ : Component (ZMod p))]).all (fun component =>
        !(component.circuit.channels.map RawChannel.name).contains (WritePermissionProvider.channel (p := p)).toRaw.name) = true := rfl
    apply WritePermission.pulls_of_silent
    intro used
    have silent := List.all_eq_true.mp checked component resource
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
    contradiction

private theorem read_member
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment) :
    (none, env) ∈ TransitionView.readIndexedRows indices (queueTables witness) := by
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp member
  simp only [TransitionView.readIndexedRows, indices, queueTables, List.zip_cons_cons, List.flatMap_cons]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨physical, physicalMem, rfl⟩)

private theorem read_edge (env : Environment (ZMod p)) :
    edge (none, env) = ((HostHintReadCoverage.input env).previous, (HostHintReadCoverage.input env).next) := rfl

private theorem timeline_at_prefix (initialClock : ℕ) (cpu prior rest : List (ExecutionRow p))
    (event : ExecutionRow p) (split : cpu = prior ++ event :: rest) :
    (eventTimeline (cpu.map ExecutionRow.event) initialClock).start prior.length =
      initialClock + (prior.map ExecutionRow.duration).sum := by
  rw [eventTimeline_start_le _ _ _ (by simp only [List.length_map, split, List.length_append, List.length_cons]; omega)]
  rw [← List.map_take, split, List.take_left, List.map_map]
  simp only [Function.comp_def, ExecutionRow.event_duration]

private theorem trajectory_at_prefix (policy : HostPolicy) (program : Target.GuestProgram)
    (source : ExecutionState) (cpu prior rest : List (ExecutionRow p)) (event : ExecutionRow p)
    (split : cpu = prior ++ event :: rest) :
    executionTrajectory policy program source (cpu.map ExecutionRow.event) prior.length =
      replayEvents? policy program source (prior.map ExecutionRow.event) := by
  simp only [executionTrajectory, ← List.map_take, split, List.take_left]

private theorem registers_of_prefix (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (silent : ∀ component ∈ (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources), Channels.programChannel.toRaw ∉ component.circuit.channels)
    (data : ProverData (ZMod p)) (sameData : witness.data = data)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (split : cpu = prior ++ event :: rest)
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map
      (handlerTable witness).environment)
    (clock : StateMsg.timeNat (event.edge data).1 = eventTime (none, env))
    (current : ExecutionState)
    (replayed : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (prior.map ExecutionRow.event) = some current)
    (currency : ∀ mp ∈ (event.facts data).memPulls,
      LocalValueAtG (fun n => (executionTrajectory ⟨{ readOnly := image.readOnly }, p⟩
        (image.toGuestProgram valid) source.realize (cpu.map ExecutionRow.event) n).map ExecutionState.sail)
        source.sail.realize (eventTimeline (cpu.map ExecutionRow.event) source.clock)
        (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    (HostReadContext.ofSail current.sail).register 5 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.code) ∧
      (HostReadContext.ofSail current.sail).register 10 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.arg1) ∧
      (HostReadContext.ofSail current.sail).register 11 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.arg2) := by
  subst data
  have cpuMember : event ∈ LocalCore.executionRows (HostLocalCore.localWitness witness) := by
    apply cpuExhaustive.mem_iff.mp
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨physical, active, sameCall, sameEvent⟩ := call_cpu_at witness
    interface constraints balanced (none, env) (read_member _ env member) event cpuMember clock
  have time := HostLocalCore.executionRow_time witness
    (auxiliaryInterface interface) constraints balanced cpuExhaustive cpuWalk prior rest event split
  have atTime := time.trans (timeline_at_prefix source.clock cpu prior rest event split).symm
  have atState := (trajectory_at_prefix ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
    source.realize cpu prior rest event split).trans replayed
  rw [sameEvent] at atTime currency
  have registers := HostLocalCore.hostCall_registers valid witness
    silent constraints balanced physical active _ source.sail.realize current.sail _ prior.length
    (congrArg (Option.map ExecutionState.sail) atState) atTime currency
  rw [sameCall] at registers
  exact registers

/-- HINT_READ dispatch and its exact padded RAM writes now use the actual replayed host queue.
The preceding replay, running status, and the grounding engine's register currency remain
semantic inputs. Program balance authenticates the operand indices and currency supplies all
three current observations; dispatch and write inventory need no prior Memory guarantees. -/
theorem run_of_source_prefix {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (split : cpu = prior ++ event :: rest)
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable (HostHintQueueBoundary.expanded witness)).table.map
      (handlerTable (HostHintQueueBoundary.expanded witness)).environment)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = eventTime (none, env))
    (current : ExecutionState)
    (replayed : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (prior.map ExecutionRow.event) = some current)
    (running : current.host.exitCode = none)
    (currency : ∀ mp ∈ (event.facts witness.data).memPulls,
      LocalValueAtG (fun n => (executionTrajectory ⟨{ readOnly := image.readOnly }, p⟩
        (image.toGuestProgram valid) source.realize (cpu.map ExecutionRow.event) n).map ExecutionState.sail)
        source.sail.realize (eventTimeline (cpu.map ExecutionRow.event) source.clock)
        (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ store bytes remaining, HintQueue.Extends store (HintQueue.ofList source.host.io.hints).1 ∧
      current.host.io.hints = bytes :: remaining ∧
      (HostHintReadCoverage.input env).next.Binds store remaining ∧
      current.host.run ⟨{ readOnly := image.readOnly }, p⟩ (.ofSail current.sail) =
        some (HostHintReadChip.execution (HostHintReadCoverage.input env) current.host bytes remaining) ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env)
          (wordTables (HostHintQueueBoundary.expanded witness)))).map HintReadWrites.produced).Perm
        (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes) := by
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final) (bankFinal := bankFinal)
    (source_interface (p := p) source.host.io.hints)
  have registers := registers_of_prefix valid (HostHintQueueBoundary.expanded witness) interface
    (source_program_silent source final bankFinal) witness.data rfl (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced) cpuExhaustive cpuWalk
    prior rest event split env member clock current replayed currency
  obtain ⟨store, extension, binding⟩ := source_current witness constraints balanced cpuExhaustive cpuWalk
    prior rest event split (none, env) (read_member (HostHintQueueBoundary.expanded witness) env member)
    clock _ _ current replayed
  rw [read_edge] at binding
  obtain ⟨bytes, remaining, hints, next, executed, writes⟩ := run_of_authenticated_witness
    (HostHintQueueBoundary.expanded witness) interface (source_permission_pulls source final bankFinal)
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced) _
    (HostHintQueueBoundary.source_authentication witness constraints) env member
    current.host store extension binding running (.ofSail current.sail) registers.1 registers.2.1 registers.2.2
  exact ⟨store, bytes, remaining, extension, hints, next, executed, writes⟩

/-- An installed HINT_LEN return is the actual current host queue's observation, derived from
the preceding replay and AIR. This conclusion requires no Memory-channel guarantees. -/
theorem length_of_source_prefix {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (ExecutionRow p)) (event : ExecutionRow p) (split : cpu = prior ++ event :: rest)
    (empty : Bool) (env : Environment (ZMod p))
    (member : (some empty, env) ∈ TransitionView.readIndexedRows indices
      (queueTables (HostHintQueueBoundary.expanded witness)))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = eventTime (some empty, env))
    (policy : HostPolicy) (program : Target.GuestProgram) (current : ExecutionState)
    (replayed : replayEvents? policy program source.realize (prior.map ExecutionRow.event) = some current) :
    Word.toBitVec64 (valueFromOffset HostHintLengthChip.Inputs 0 env).call.result = current.host.io.hintLength := by
  obtain ⟨store, extension, binding⟩ := source_current witness constraints balanced cpuExhaustive cpuWalk
    prior rest event split (some empty, env) member clock policy program current replayed
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final) (bankFinal := bankFinal)
    (source_interface (p := p) source.host.io.hints)
  have authentication := HostHintQueueBoundary.source_authentication witness constraints
  have specs := queue_specs (HostHintQueueBoundary.expanded witness) interface _ authentication checks balance
  have advance := HostQueueHistory.advance (some empty, env) _
    (rows_spec _ (queueTables_aligned (HostHintQueueBoundary.expanded witness)) specs _ member)
    (HostQueueHistory.records_of_witness (HostHintQueueBoundary.expanded witness) _ authentication balance _ member)
  obtain ⟨_, _, _, _, applied, _⟩ := advance store current.host.io.hints extension binding
  by_contra different
  simp only [HostQueueHistory.event, HintQueue.Event.apply?, HostIO.hintLength] at applied
  simp only [HostIO.hintLength] at different
  simp only [if_neg different, reduceCtorEq] at applied

end SP1Clean.Soundness.HostQueueCurrent
