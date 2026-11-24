import SP1Clean.Soundness.HostHintReadBankAgreement
import SP1Clean.Semantics.Host.HostReplay

/-! # Complete host reconstruction on the installed local execution

The final queue cursor and both bank endpoints agree with the same CPU path. Complete physical
call accounting excludes WRITE in this installation, so all remaining host I/O fields
are preserved from the source. Terminal status comes from actual HALT events, retaining the
semantic difference between running and exit zero. Binding a caller's complete outgoing snapshot
and the public Exit bus remains separate; no restriction is added to the all-eight-call target.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Semantics HostHintReadLocal NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {extra : List (Component (ZMod p))} [GroundingResources extra]
local instance hostAgreementLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}
  {channelNames : ((HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels)).map (·.name)).Nodup}
  {tableChannels : ∀ component ∈ ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources)),
    component.circuit.channels ⊆ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels)}

private theorem inventory_calls
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names channelNames tableChannels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec) :
    ∀ row ∈ LocalCore.executionRows (HostLocalCore.localWitness witness), HostReceiptProfile.event true row.event := by
  have receivedCode := HostQueueCallProjection.calls_code witness interface constraints bytes specs
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface) constraints calls
  intro row member
  cases row with
  | instruction row => trivial
  | halt row =>
      have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness witness) 2)
          (haltRow (HostLocalCore.localWitness witness).data) (·.is_real) := by simpa [LocalCore.executionRows] using member
      have zero := HostQueueCPUReplay.halt_code (HostLocalCore.localWitness witness)
        (HostLocalCore.localWitness_constraints witness constraints) row active
      change HostReceiptProfile.code true (Word.toBitVec64 row.x5_memory.prev_value)
      rw [zero]
      exact ⟨.halt, by decide, rfl⟩
  | syscall row =>
      have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness witness) 3)
          (syscallInstrsRow (HostLocalCore.localWitness witness).data) (·.is_real) := by simpa [LocalCore.executionRows] using member
      rw [← HostLocalCore.hostCallTable_projection] at active
      obtain ⟨env, envMem, rfl⟩ := List.mem_map.mp active
      have received := handoff.mem_iff.mp (List.mem_map_of_mem (f := HostCallLedger.call) envMem)
      simpa only [HostReceiptProfile.code, HostReceiptProfile.event, ExecutionRow.event, rawCode_syscallEventOfRow,
        HostCallLedger.call, HostCallChip.message, Word.toBitVec64, Word.toNat]
        using receivedCode _ received

private theorem queue_terminal
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names channelNames tableChannels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (specs : ∀ table ∈ queueTables witness, table.Spec)
    {cpu : List (ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    {path : List (HostQueueOrder.Row (p := p))} {initial final : HostHintQueue.State (ZMod p)}
    {upper : HintQueue.Store}
    (queueExhaustive : path.Perm (HostQueueOrder.activeRows (queueTables witness)))
    (queueWalk : Walk.IsWalk HostQueueOrder.edge initial final path)
    (history : HostHintQueueHistory.History source.host.io.hints final upper path)
    (policy : HostPolicy) (program : Target.GuestProgram) (target : ExecutionState)
    (replay : replayEvents? policy program source.realize (cpu.map ExecutionRow.event) = some target) :
    HintQueue.decode? upper (Address.toNat final.head) = some target.host.io.hints := by
  have projected := HostQueueCPUReplay.cpu_projection witness interface constraints calls bytes ordering specs
    exhaustive walk queueExhaustive queueWalk
  have erased := congrArg (List.map Prod.snd) projected
  simp only [HostQueueCPUReplay.stampedCPU, List.map_filterMap, Option.map_map, Function.comp_def,
    Option.map_id_fun', id_eq, List.map_map] at erased
  have safe := HostQueueCPUReplay.cpu_safe witness interface constraints calls bytes specs
  have actual := replayEvents?_queue (fun event member => by
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
    exact safe row (exhaustive.mem_iff.mp rowMem)) replay
  simp only [List.filterMap_map, Function.comp_def] at actual
  rw [erased] at actual
  obtain ⟨remaining, replayed, decoded⟩ := HostHintQueueHistory.terminal_bytes history
  exact decoded.trans (replayed.symm.trans actual)

variable {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
variable [sourceRegistration : HostFinalMemory.Registration image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels]
  {sourceNames : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints)}

/-- The terminal queue cursor authenticates the actual replay's remaining complete hint bytes. -/
theorem GroundingCarrier.final_hints (valid : image.Valid)
    {witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) (target : ExecutionState)
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) =
      some target.host.io.hints := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := GroundingResources.sourceInterface (p := p) source.host.io.hints extra
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have records := HostHintQueueBoundary.record_channels witness balanced
  obtain ⟨path, exhaustive, walk, history⟩ := HostHintQueueHistory.source_history witness constraints balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have terminal := queue_terminal (HostHintQueueBoundary.projected witness) interface checks calls records.byte ordering
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks records)
    carrier.exhaustive
  simp only [HostHintQueueBoundary.projected_data, HostHintQueueBoundary.projected_publicInput] at terminal
  exact terminal carrier.cpuWalk exhaustive walk history _ _ target replay

/-- Every event of the physical CPU inventory belongs to the installed seven-call profile. -/
theorem installed_events
    (witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames)
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) :
    ∀ event ∈ (LocalCore.executionRows (HostLocalCore.localWitness
      (HostHintQueueBoundary.projected witness))).map ExecutionRow.event, HostReceiptProfile.event true event := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := GroundingResources.sourceInterface (p := p) source.host.io.hints extra
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have records := HostHintQueueBoundary.record_channels witness balanced
  have admitted := inventory_calls (HostHintQueueBoundary.projected witness) interface checks calls records.byte
    (queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks records)
  intro event member
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp member
  exact admitted row rowMem

/-- The installed AIR derives the host frame from its complete receiver inventory. -/
theorem GroundingCarrier.host_frame_safe
    {witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) :
    ∀ event ∈ carrier.events, HostFrameSafe event := by
  intro event member
  have admitted := installed_events witness constraints balanced event
    ((carrier.exhaustive.map ExecutionRow.event).mem_iff.mp member)
  cases event with
  | ordinary => trivial
  | syscall call => exact HostReceiptProfile.ne_write (includeVerify := true) admitted

/-- All host fields are recovered on the same path: authenticated hints and banks, preserved
external I/O, and the exact optional terminal status from actual events. -/
theorem GroundingCarrier.final_host (valid : image.Valid)
    {witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) (target : ExecutionState)
    (path : ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events target) :
    ∃ hints, HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      target.host = { source.host with
        io.hints := hints
        committed := bankFinal.committed
        deferred := bankFinal.deferred
        exitCode := carrier.events.foldl hostExitAfter source.host.exitCode } := by
  have banks := carrier.final_banks valid constraints balanced target path.replay
  have hints := carrier.final_hints valid constraints balanced target path.replay
  have frame := path.host_frame (carrier.host_frame_safe constraints balanced)
  exact ⟨target.host.io.hints, hints, by simpa only [banks.1, banks.2, path.host_exit, ExecutionSnapshot.realize] using frame⟩

/-- Raw installed AIR reconstructs a local path and its complete final host, alongside the
existing final PC/clock/Memory-frontier agreement. No host frame, order, or replay premise is added. -/
theorem source_execution_with_host (valid : image.Valid)
    (witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames)
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) :
    ∃ events target hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value)) ∧
      HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      target.host = { source.host with
        io.hints := hints
        committed := bankFinal.committed
        deferred := bankFinal.deferred
        exitCode := events.foldl hostExitAfter source.host.exitCode } := by
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness constraints balanced
  obtain ⟨target, path, clock, pc, memory⟩ := carrier.execution valid constraints balanced
  obtain ⟨hints, decoded, host⟩ := carrier.final_host valid constraints balanced target path
  exact ⟨carrier.events, target, hints, path, carrier.exhaustive.map ExecutionRow.event, clock, pc, memory, decoded, host⟩

end SP1Clean.Soundness.HostHintReadCPU
