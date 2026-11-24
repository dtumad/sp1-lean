import SP1Clean.Export.WritePhysicalKeys
import SP1Clean.Soundness.LocalCoreWordRanges
import SP1Clean.Soundness.MemoryWordRanges

/-! # Grounded word limbs for every original read-back source

The actual Memory clocks and component push requirements close the chronological
word-range induction. Receipt selection therefore preserves the exact field word
needed by the native read probe as well as its interpreted 64-bit value.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem aligned_pushes (valid : image.Valid) (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (checked : core.Constraints) (ordering : LocalCore.OrderingChannels core) (program : core.BalancedChannel programChannel.toRaw)
    (data : ProverData Fp) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows core).map (ExecutionRow.facts data)))
    (clocks : ∀ event ∈ LocalCore.executionRows core, ∀ mp ∈ (event.facts data).memPulls, MemoryMsg.ClkBound mp.1) :
    ∀ row ∈ aligned, (∀ t ∈ rowTouches row, MemoryMsg.isU64 t.1.1) → ∀ t ∈ rowTouches row, MemoryMsg.isU64 t.2 := by
  intro row included good
  obtain ⟨_, seen, fits⟩ := forall₂_exists_right paired row included
  obtain ⟨event, owner, rfl⟩ := List.mem_map.mp seen
  have pulls : (rowTouches row).map Prod.fst = row.memPulls := List.map_fst_zip fits.touches.length_eq.le
  have word {m} (member : m ∈ row.memPulls.map Prod.fst) : MemoryMsg.isU64 m := by
    rw [← pulls, List.map_map] at member
    obtain ⟨t, present, rfl⟩ := List.mem_map.mp member
    exact good _ present
  have input : ∀ mp ∈ (event.facts data).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 := by
    intro mp member
    exact ⟨word (fits.memory.pulls.mem_iff.mpr (List.mem_map_of_mem (f := Prod.fst) member)), clocks event owner mp member⟩
  have outputs := LocalCore.executionRows_word_ranges valid core checked ordering.byte program owner
    (event.facts_setData data core.data ▸ input)
  intro t member
  have push := fits.memory.pushes.mem_iff.mp (List.of_mem_zip member).2
  rw [event.facts_setData data core.data] at push
  exact outputs _ push

private theorem cpu_clocks (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source)) (data : ProverData Fp)
    (words : List (HintReadCoverage.Row (p := SP1Prime))) :
    let cpu := LocalCore.executionRows core
    let rows := cpu.map (eventFacts data words)
    (∀ loc, ∀ msg ∈ Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
        pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _),
      MemoryClockBounds msg) → ∀ event ∈ cpu, ∀ mp ∈ (event.facts data).memPulls, MemoryMsg.ClkBound mp.1 := by
  intro cpu rows bounded event active mp pulled
  have member : mp.1 ∈ pullsAt rows (MemoryMsg.locOf mp.1) := mem_pullsAt.mpr ⟨⟨eventFacts data words event,
    List.mem_map_of_mem (f := eventFacts data words) active, mp, List.mem_append_left _ pulled, rfl⟩, rfl⟩
  exact (bounded _ mp.1 (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr member))))).1

/-- Every live original readback has four genuine 16-bit value limbs, derived from
the realized source, the signed Memory history and the actual checked component providers. -/
theorem live_words_canonical (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw) (program : witness.BalancedChannel programChannel.toRaw)
    (boundaries : ∀ channel ∈ (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel) :
    ∀ record ∈ Counted.live (records (raw witness)), Word.isU64 record.value := by
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  let cpu := LocalCore.executionRows core
  let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
  let extra := (cpu.flatMap (wordsAt boundary.data words)).map touch
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  have membership (ch) (member : ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) : core.BalancedChannel ch := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith ch)
    rw [core_membership_ledger witness ch member]
    exact boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  obtain ⟨aligned, paired, histories⟩ := physical_record_chains valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  have fetch : core.BalancedChannel programChannel.toRaw := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith programChannel.toRaw)
    rwa [core_program_ledger witness]
  have bounded := consumed_clock_bounds valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program
    (fun ch present => boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)))
  have clocks := cpu_clocks core boundary.data words bounded
  have wordsWell := MemoryRecordChain.words_of_histories aligned extra (LocalCore.memoryRefreshes core)
    (LocalCore.memoryInitialFrontier core) (LocalCore.memoryFinalFrontier core) histories
    (fun _ _ present => (LocalCore.memoryInitialFrontier_content_of_channels core physical ordering.sourceChecks ordering.byte membership present).2.1.1)
    (fun row present t selected => (List.forall₂_iff_zip.mp (forall₂_exists_right paired row present).choose_spec.2.touches).2 selected)
    (aligned_pushes valid core physical ordering fetch boundary.data aligned paired clocks)
    (by
      intro t selected
      obtain ⟨row, member, rfl⟩ := List.mem_map.mp selected
      obtain ⟨_, _, inside⟩ := List.mem_flatMap.mp member
      exact (word_access witness checked bytes row (List.mem_filter.mp inside).1).value)
    (fun e present => (congrArg Prod.snd (LocalCore.memoryRefreshes_preserve core e present)).symm)
  intro record live
  obtain ⟨prior, _, value, funding⟩ := physical_representative witness checked packet installed packetChecked balanced cursor wordData bytes boundary.data aligned paired record live
  rw [value]
  rcases funding with ⟨next, member⟩ | member
  · exact wordsWell.1 (prior, next) member
  · have hostChecked := HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked))
    have finalOrder : (hostWitness witness).BalancedChannel (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
      change BalancedInteractions ((hostWitness witness).interactionsWith _)
      rw [host_core_ledger witness _ (by simp [LocalCore.baseEnsemble])]
      exact boundaries _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have unique := (HostLocalCore.final_records_canonical_nodup (hostWitness witness)
      (HostHintReadLocal.source_boundary_silent source _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hostChecked ordering.byte finalOrder).2
    exact wordsWell.2 (MemoryMsg.locOf prior) prior (head_at_unique _ unique member)

end SP1Clean.Export.WriteSourceRegistry
