import SP1Clean.Export.WriteMemoryReplay
import SP1Clean.Proofs.Completeness.WriteCountedTables

/-! # Clock bounds for the full original Memory ledger

The physical frontier equation transfers range checks from source records, CPU writes and
refresh writes to every consumed record. The HINT_READ words use their two installed tables'
Byte guarantees. This breaks the timestamp dependency before chronological replay.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

/-- The original instruction fetch ledger is untouched by the CPU and host projections. -/
theorem core_program_ledger (witness : EnsembleWitness (HostObserved.ensemble image source target final)) :
    (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith programChannel.toRaw =
      witness.interactionsWith programChannel.toRaw :=
  (HostLocalCore.localWitness_program (hostWitness witness) (HostHintReadLocal.source_program_silent source)).trans
    (host_core_ledger witness _ (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels]))

/-- The two fixed source tables retain the complete address and word membership ledgers. -/
theorem core_membership_ledger (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (ch : RawChannel Fp) (member : ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) :
    (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith ch = witness.interactionsWith ch :=
  (HostLocalCore.localWitness_membership (hostWitness witness) ch member
    (HostHintReadLocal.source_boundary_silent source ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))).trans
    (host_core_ledger witness ch (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [LocalCore.baseEnsemble]))

/-- Byte checks on the two physical word tables establish their RAM access and write-time
facts independently of any assumed truth about a prior Memory record. -/
theorem word_access (witness : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : witness.Constraints)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw) :
    ∀ row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness)), HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram := by
  apply HostHintReadLocal.word_touches_of_guarantees (hostWitness witness)
    (HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  intro table present
  obtain ⟨last, rfl⟩ := word_table_eq witness present
  exact bytes last

private theorem consumed_of_balance (valid : image.Valid) (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (data : ProverData Fp) (words : List (HintReadCoverage.Row (p := SP1Prime)))
    (physical : core.Constraints) (ordering : LocalCore.OrderingChannels core) (fetch : core.BalancedChannel programChannel.toRaw)
    (fixed : ∀ ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot, core.BalancedChannel ch)
    (access : ∀ word ∈ words, HostRamTouches.AccessFacts (HintReadCoverage.rowInput word).ram)
    (loc : MemLoc) :
    let rows := (LocalCore.executionRows core).map (eventFacts data words)
    let supply := Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (LocalCore.sourceWitness core)) : Multiset _) +
      pushesAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((LocalCore.memoryRefreshes core).map Prod.snd) : Multiset _)
    let consumed := Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
      pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _)
    supply = consumed → ∀ msg ∈ consumed, MemoryClockBounds msg := by
  intro rows supply consumed balance
  have sourceSpecs := LocalCore.sourceTables_spec_of_channels core physical ordering.byte fixed
  have authentic := (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables _ sourceSpecs
  have refresh := LocalCore.memoryRefreshes_push_bounds_of_byte core physical ordering.byte
  refine forall_mem_of_balance (G := MemoryClockBounds) balance ?_
  intro msg member
  rcases Multiset.mem_add.mp member with sourceOrCPU | refreshed
  · rcases Multiset.mem_add.mp sourceOrCPU with initial | pushed
    · have initialFacts := authentic msg (Multiset.mem_coe.mp (Multiset.mem_filter.mp initial).1)
      exact ⟨initialFacts.2.1, clkHigh_lt_of_timeNat_le (le_of_eq initialFacts.2.2.1) (by norm_num)⟩
    obtain ⟨row, rowMem, emitted, _⟩ := mem_pushesAt.mp pushed
    obtain ⟨event, present, rfl⟩ := List.mem_map.mp rowMem
    rcases List.mem_append.mp emitted with original | wordMem
    · exact LocalCore.executionRows_push_bounds_of_channels valid core physical ordering fetch data present original
    obtain ⟨word, selected, rfl⟩ := List.mem_map.mp wordMem
    have localAccess := access word (List.mem_filter.mp selected).1
    exact ⟨localAccess.pushLow, localAccess.pushHigh⟩
  · obtain ⟨pair, inRefreshes, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp (Multiset.mem_filter.mp refreshed).1)
    exact refresh pair inRefreshes

/-- All consumed records, including physical refresh priors and terminal records, have
bounded clock limbs on the eight-call execution. -/
theorem consumed_clock_bounds (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw) (program : witness.BalancedChannel programChannel.toRaw)
    (membership : ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot, witness.BalancedChannel channel)
    (loc : MemLoc) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let rows := sourceExecutionRows (HostFinalMemory.baseWitness (HostObserved.baseWitness witness))
    ∀ msg ∈ Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
        pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _),
      MemoryClockBounds msg := by
  intro core rows
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  have fetch : core.BalancedChannel programChannel.toRaw := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith programChannel.toRaw)
    rwa [core_program_ledger witness]
  have fixed (ch) (member : ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) : core.BalancedChannel ch := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith ch)
    rw [core_membership_ledger witness ch member]
    exact membership ch member
  exact consumed_of_balance valid core boundary.data _ physical ordering fetch fixed (word_access witness checked bytes) loc
    (execution_memory_balance witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory loc)

/-- Changing prover data preserves the original checked CPU and word-row facts. -/
theorem eventFacts_setData (event : ExecutionRow SP1Prime) (left right : ProverData Fp)
    (words : List (HintReadCoverage.Row (p := SP1Prime))) : eventFacts left words event = eventFacts right words event := by
  unfold eventFacts wordsAt cpuClock
  rw [event.facts_setData left right, event.edge_setData left right]

private theorem bounded_of_sources (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (checked : core.Constraints) (ordering : LocalCore.OrderingChannels core)
    (data : ProverData Fp) (words : List (HintReadCoverage.Row (p := SP1Prime)))
    (bounded : ∀ loc, ∀ msg ∈ Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
      pullsAt ((LocalCore.executionRows core).map (eventFacts data words)) loc +
      Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _), MemoryClockBounds msg)
    (record : Readback Fp)
    (source : (∃ event ∈ LocalCore.executionRows core, ∃ prior time, (prior, time) ∈ (eventFacts core.data words event).memPulls ∧
        record = AccessSupply.atClock (cpuClock core.data event) prior) ∨
      (∃ prior next, (prior, next) ∈ LocalCore.memoryRefreshes core ∧ record = AccessSupply.atClock (next.clk_high, next.clk_low) prior) ∨
      ∃ prior ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness core), record = finalReadback prior) : Counted.Bounded record := by
  rcases source with ⟨event, active, prior, time, pulled, rfl⟩ | ⟨prior, next, present, rfl⟩ | ⟨prior, present, rfl⟩
  · rw [eventFacts_setData event core.data data words] at pulled
    have priorBound := bounded (MemoryMsg.locOf prior) prior (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr
      (mem_pullsAt.mpr ⟨⟨_, List.mem_map_of_mem (f := eventFacts data words) active, (prior, time), pulled, rfl⟩, rfl⟩)))))
    have high := (LocalCore.executionRows_good_of_orderingChannels core checked ordering active).1.1
    have low := (LocalCore.executionRows_clock_of_orderingChannels core checked ordering active).2.2.2
    exact ⟨priorBound.2, priorBound.1, high, low⟩
  · have priorBound := bounded (MemoryMsg.locOf prior) prior (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr (List.mem_map_of_mem (f := Prod.fst) present), rfl⟩)))
    have nextBound := LocalCore.memoryRefreshes_push_bounds_of_byte core checked ordering.byte (prior, next) present
    exact ⟨priorBound.2, priorBound.1, nextBound.2, nextBound.1⟩
  · have priorBound := bounded (MemoryMsg.locOf prior) prior (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr present, rfl⟩)))))
    have ceiling : (16777215 : Fp).val < 2 ^ 24 := by decide
    exact ⟨priorBound.2, priorBound.1, ceiling, ceiling⟩

/-- Every live predecessor on all 31 physical publishers has both original clock limbs
in range. This supplies the counted-table compiler's range condition for the entire tape. -/
theorem live_records_bounded (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw) (program : witness.BalancedChannel programChannel.toRaw)
    (membership : ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot, witness.BalancedChannel channel)
    : ∀ record ∈ Counted.live (records (raw witness)), Counted.Bounded record := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  have bounded := consumed_clock_bounds valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program membership
  intro record present
  obtain ⟨⟨gate, record⟩, active, rfl⟩ := List.mem_map.mp present
  obtain ⟨member, isOne⟩ := List.mem_filter.mp active
  have gateOne : gate = 1 := of_decide_eq_true isOne
  have positive : gate ≠ 0 := by rw [gateOne]; exact one_ne_zero
  obtain ⟨id, origin⟩ := origin_of_record (raw witness) (raw_registered witness) member positive
  exact bounded_of_sources core physical ordering boundary.data words bounded record
    (source_attribution witness checked packet installed packetChecked balanced cursor wordData bytes id record origin)

end SP1Clean.Export.WriteSourceRegistry
