import SP1Clean.Export.WriteMemoryReplayTiming
import SP1Clean.Soundness.MemoryRecordChain

/-! # Reconstructing each location's original signed Memory history

The physical two-limb clock bounds remove the remaining proviso from timestamp comparison.
The per-location history contains every original CPU touch, every HINT_READ word and every
physical refresh. No incoming word or timestamp is assumed current.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem record_chains (valid : image.Valid) (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (checked : core.Constraints) (ordering : LocalCore.OrderingChannels core) (program : core.BalancedChannel programChannel.toRaw)
    (data : ProverData Fp) (words : List (HintReadCoverage.Row (p := SP1Prime)))
    (accesses : ∀ word ∈ words, HostRamTouches.AccessFacts (HintReadCoverage.rowInput word).ram) :
    let cpu := LocalCore.executionRows core
    let rows := cpu.map (eventFacts data words)
    let additional := (cpu.flatMap (wordsAt data words)).map touch
    let refresh := LocalCore.memoryRefreshes core
    (∀ loc, optMS (LocalCore.memoryInitialFrontier core loc) + pushesAt rows loc +
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.snd) : Multiset _) =
      optMS (LocalCore.memoryFinalFrontier core loc) + pullsAt rows loc +
        Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.fst) : Multiset _)) →
    (∀ loc, ∀ msg ∈ Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
      pullsAt rows loc + Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.fst) : Multiset _), MemoryClockBounds msg) →
    ∃ aligned, List.Forall₂ AlignedFacts aligned (cpu.map (ExecutionRow.facts data)) ∧
      ∀ loc, MemoryRecordChain.History (MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned additional refresh))
        (LocalCore.memoryInitialFrontier core loc) (LocalCore.memoryFinalFrontier core loc) := by
  intro cpu rows additional refresh balance bounded
  obtain ⟨aligned, paired⟩ := align_rows data cpu (by
    intro e member
    obtain ⟨r, facts⟩ := LocalCore.executionRows_aligned_of_channels valid core checked ordering.byte program member
    exact ⟨r, e.facts_setData core.data data ▸ facts⟩)
  have retained {r} (active : r ∈ aligned) : ∃ original ∈ cpu.map (ExecutionRow.facts data), AlignedFacts r original :=
    forall₂_exists_right paired _ active
  have hostFact {t : Touch SP1Prime} (present : t ∈ additional) :
      MemoryMsg.locOf t.1.1 = MemoryMsg.locOf t.2 ∧ (MemoryClockBounds t.1.1 → MemoryMsg.timeNat t.1.1 < MemoryMsg.timeNat t.2) := by
    obtain ⟨word, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨event, _, selected⟩ := List.mem_flatMap.mp member
    have facts := accesses word (List.mem_filter.mp selected).1
    exact ⟨facts.touch.loc_eq.symm, fun prior => facts.order prior.1⟩
  have advance := LocalCore.memoryRefreshes_order_of_bounds core checked ordering.byte (by
    intro pair member
    exact bounded (MemoryMsg.locOf pair.1) pair.1 (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr (List.mem_map_of_mem (f := Prod.fst) member), rfl⟩))))
  refine ⟨aligned, paired, fun loc => ?_⟩
  let edges := MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned additional refresh)
  have split := MemoryRecordChain.projections aligned additional refresh loc
    (fun r member => (retained member).choose_spec.2.touches) (fun _ active => (hostFact active).1)
    (fun pair member => congrArg Prod.fst (LocalCore.memoryRefreshes_preserve core pair member))
  have original := rowAggregates_of_permutation (paired.imp fun _ _ h => h.memory) loc
  have all := eventFacts_memory data words cpu loc
  have pushes : (↑(edges.map Prod.snd) : Multiset _) = pushesAt rows loc +
      Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.snd) : Multiset _) := by
    rw [split.1, original.1, all.1]
    simp only [additional, List.map_map, Function.comp_def]
  have pulls : (↑(edges.map Prod.fst) : Multiset _) = pullsAt rows loc +
      Multiset.filter (fun m => MemoryMsg.locOf m = loc) (↑(refresh.map Prod.fst) : Multiset _) := by
    rw [split.2, original.2, all.2]
    simp only [additional, List.map_map, Function.comp_def]
  apply MemoryRecordChain.exists_walk
  · rw [pushes, pulls, ← add_assoc, ← add_assoc]
    exact balance loc
  intro pair present
  have prior : MemoryClockBounds pair.1 := by
    have pulled := Multiset.mem_coe.mpr (List.mem_map_of_mem (f := Prod.fst) present)
    rw [pulls] at pulled
    apply bounded loc pair.1
    rw [add_assoc]
    exact Multiset.mem_add.mpr (Or.inr pulled)
  rcases List.mem_append.mp (List.mem_filter.mp present).1 with executed | bumped
  · obtain ⟨t, selected, rfl⟩ := List.mem_map.mp executed
    rcases List.mem_append.mp selected with instruction | host
    · obtain ⟨r, row, member⟩ := List.mem_flatMap.mp instruction
      exact (retained row).choose_spec.2.slot t member prior.1 prior.2
    · exact (hostFact host).2 prior
  · exact advance pair bumped

/-- Every location in the eight-call execution has either an empty history or a single
chronological physical record chain between its two genuine Memory endpoints. -/
theorem physical_record_chains (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
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
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
    let cpu := LocalCore.executionRows core
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
    let additional := (cpu.flatMap (wordsAt boundary.data words)).map touch
    ∃ aligned, List.Forall₂ AlignedFacts aligned (cpu.map (ExecutionRow.facts boundary.data)) ∧
      ∀ loc, MemoryRecordChain.History
        (MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned additional (LocalCore.memoryRefreshes core)))
        (LocalCore.memoryInitialFrontier core loc) (LocalCore.memoryFinalFrontier core loc) := by
  intro core boundary cpu words additional
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  have fetch : core.BalancedChannel programChannel.toRaw := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith programChannel.toRaw)
    rwa [core_program_ledger witness]
  exact record_chains valid core physical ordering fetch boundary.data words (word_access witness checked bytes)
    (execution_memory_frontier witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory boundaries)
    (consumed_clock_bounds valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program
      (fun ch member => boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))))

end SP1Clean.Export.WriteSourceRegistry
