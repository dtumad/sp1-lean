import SP1Clean.Export.WriteBoundarySourceGrounding
import SP1Clean.Export.WriteHostSourceGrounding
import SP1Clean.Soundness.WritePacketReceiver

/-! # HINT_READ word ownership in the complete host dispatch

The signed HostCall ledger includes the installed WRITE packet receiver. Every positive
HINT_READ word follows the genuine word-cursor chain to a HINT_READ handler, whose full
payload identifies an actual ECALL in this complete dispatch.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness Channels WriteProbe WriteProbe.AccessInventory
open HostHintReadCPU NativeCore

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

/-- All eight receivers exhaust the active CPU calls. The added packet table contributes
its signed ledger before padding is filtered and each repeated payload is counted. -/
theorem eight_calls (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    (packet : Table Fp) (installed : packet.component = WritePacket.component) (packetChecked : packet.Constraints)
    (balanced : BalancedInteractions (witness.interactionsWith HostCallChip.channel.toRaw ++
      packet.interactionsWith HostCallChip.channel.toRaw)) :
    let host := hostWitness witness
    (HostCallLedger.calls (HostLocalCore.hostCallTable host) host.data).Perm
      (HostLocalHandoff.calls host ++ ReceiverView.tableMessages WritePacket.receiver packet) := by
  intro host
  have interface := GroundingResources.sourceInterface (p := SP1Prime) source.host.io.hints
    (FinalMemoryChecks.checkTables target.sail.memorySnapshot)
  have physical := HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _
    (HostObserved.baseWitness_constraints witness checked))
  apply HostCallLedger.calls_perm _ host.data (HostLocalCore.hostCallTable_component host)
    (physical _ (HostLocalCore.hostCallTable_mem host))
  rw [← host_protocol_ledger witness HostCallChip.channel.toRaw (List.mem_cons_self ..)] at balanced
  have selected := balanced.filter_nonzero
  rw [HostLocalHandoff.hostCall_interactions host (HostHintReadLocal.resources_hostCall_silent interface), List.filter_append,
    List.filter_append, ReceiverView.messages_interactions _ _ (HostLocalHandoff.receiverTables_aligned host)
      (fun table member => physical table (List.mem_of_mem_drop (List.mem_of_mem_take member))),
    WritePacket.active_call_ledger packet installed packetChecked, List.append_assoc, ← List.map_append] at selected
  exact selected

/-- Every active HINT_READ word follows the original cursor to a handler carrying the exact
CPU call. The two word tables use their physical byte ranges and authenticated hint-word
records, including records supplied by earlier hint allocations. -/
theorem word_cpu_eight (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    (packet : Table Fp) (installed : packet.component = WritePacket.component) (packetChecked : packet.Constraints)
    (balanced : BalancedInteractions (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (row : HintReadCoverage.Row (p := SP1Prime))
    (member : row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness))) :
    let host := hostWitness witness
    ∃ handler ∈ (HostHintReadLocal.handlerTable host).table.map (Environment.fromArray · host.data),
      ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable host) host.data,
        HostCallLedger.call env = (HostHintReadCoverage.input handler).call ∧
        ExecutionRow.syscall (HostCallLedger.input env) ∈ LocalCore.executionRows (HostLocalCore.localWitness host) ∧
        cpuClock host.data (.syscall (HostCallLedger.input env)) = wordClock row := by
  intro host
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  have boundaryChecked := HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)
  have physical := HostHintQueueBoundary.projected_constraints boundary boundaryChecked
  have interface := GroundingResources.sourceInterface (p := SP1Prime) source.host.io.hints
    (FinalMemoryChecks.checkTables target.sail.memorySnapshot)
  have localGuarantees (ch : RawChannel Fp) (valid : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees ch) :
      ∀ table ∈ HostHintReadLocal.wordTables host, table.ChannelGuarantees ch := by
    intro table inside
    obtain ⟨last, rfl⟩ := word_table_eq witness inside
    exact valid last
  have localCursor : host.BalancedChannel HintReadWordChip.stateChannel.toRaw := by
    change BalancedInteractions ((hostWitness witness).interactionsWith HintReadWordChip.stateChannel.toRaw)
    rwa [host_protocol_ledger witness _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
  have steps := HostHintReadLocal.word_steps_of_guarantees host physical (localGuarantees _ bytes) (localGuarantees _ wordData)
  have dispatch := eight_calls witness checked packet installed packetChecked balanced
  exact word_cpu_of_received host interface (fun _ seen => dispatch.mem_iff.mpr (List.mem_append_left _ seen)) localCursor steps row member


private theorem cpuClock_data (event : ExecutionRow SP1Prime) (left right : ProverData Fp) :
    cpuClock left event = cpuClock right event := by simp only [cpuClock, event.edge_setData left right]

/-- All positively authenticated source intervals have one of three physical origins on
this exact CPU tape and Memory inventory. CPU intervals end at the event's incoming State,
refresh intervals end at the refreshed timestamp, and finalizers cover their suffix. -/
theorem source_attribution (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    (packet : Table Fp) (installed : packet.component = WritePacket.component) (packetChecked : packet.Constraints)
    (balanced : BalancedInteractions (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (id : Source) (record : Readback Fp) (origin : Origin (raw witness) id record) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
    (∃ event ∈ LocalCore.executionRows core, ∃ prior time, (prior, time) ∈ (eventFacts core.data words event).memPulls ∧
      record = AccessSupply.atClock (cpuClock core.data event) prior) ∨
      (∃ prior next, (prior, next) ∈ LocalCore.memoryRefreshes core ∧ record = AccessSupply.atClock (next.clk_high, next.clk_low) prior) ∨
      ∃ prior ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness core), record = finalReadback prior := by
  intro core words
  cases id with
  | ordinary tag =>
    obtain ⟨row, present, prior, time, pulled, same⟩ := ordinary_event_of_origin witness checked tag record origin
    exact Or.inl ⟨.instruction row, present, prior, time, List.mem_append_left _ pulled, same⟩
  | refresh => exact Or.inr (Or.inl (refresh_of_origin witness checked origin))
  | finalizer ram => exact Or.inr (Or.inr (final_of_origin witness checked ram origin))
  | host family =>
    cases family with
    | ecall =>
      obtain ⟨row, present, prior, time, pulled, same⟩ := syscall_event_of_origin witness checked origin
      exact Or.inl ⟨.syscall row, present, prior, time, List.mem_append_left _ pulled, same⟩
    | word last =>
      obtain ⟨row, active, same⟩ := word_of_origin witness checked last origin
      obtain ⟨_, _, env, _, _, present, clock⟩ := word_cpu_eight witness checked packet installed packetChecked balanced cursor wordData bytes row active
      let call := ExecutionRow.syscall (HostCallLedger.input env)
      have atClock : cpuClock core.data call = wordClock row := (cpuClock_data call core.data (hostWitness witness).data).trans clock
      refine Or.inl ⟨call, present, (touch row).1.1, (touch row).1.2, List.mem_append_right _ ?_, ?_⟩
      · exact List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨active, decide_eq_true atClock.symm⟩, rfl⟩
      · rwa [atClock]

end SP1Clean.Export.WriteSourceRegistry
