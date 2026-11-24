import SP1Clean.Export.WriteWordOwner

/-! # Memory record conservation for the eight-call CPU walk

Every HINT_READ word has a receiver on the complete signed HostCall ledger. Unique incoming
State clocks therefore attach every physical word occurrence to exactly one CPU event.
The resulting CPU groups, refresh pairs and endpoint records account for the original Memory
ledger, including the released register accesses of WRITE itself.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem cpu_clocks (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (checked : core.Constraints) (ordering : LocalCore.OrderingChannels core) (data : ProverData Fp)
    (cpu : List (ExecutionRow SP1Prime)) (exhaustive : cpu.Perm (LocalCore.executionRows core)) :
    (cpu.map (cpuClock data)).Nodup := by
  have unique := LocalCore.executionRows_clocks_nodup_of_orderingChannels core checked ordering
  simp_rw [ExecutionRow.edge_setData _ core.data data] at unique
  exact (exhaustive.map _).nodup_iff.mpr unique

/-- Eight-way signed dispatch assigns the actual word occurrences once, in any exhaustive
order of the CPU events. The assignment uses their two original clock limbs. -/
theorem words_partition (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (data : ProverData Fp) (cpu : List (ExecutionRow SP1Prime))
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))) :
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness witness))
    (cpu.flatMap (wordsAt data words)).Perm words := by
  intro words
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  apply words_partition_of_owned data words cpu (cpu_clocks core physical ordering data cpu exhaustive)
  intro row inside
  obtain ⟨_, _, env, _, _, event, same⟩ := word_cpu_eight witness checked packet installed packetChecked balanced
    cursor wordData bytes row inside
  let call := ExecutionRow.syscall (HostCallLedger.input env)
  have travel : cpuClock data call = cpuClock (hostWitness witness).data call := by
    unfold cpuClock
    rw [call.edge_setData data (hostWitness witness).data]
  exact ⟨call, exhaustive.mem_iff.mpr event, travel.trans same⟩

/-- The physical Memory ledger conserves every source, CPU, refresh and final record at
each location. The signed call balance includes the WRITE packet receiver. -/
theorem execution_memory_balance (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw) (loc : MemLoc) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let rows := sourceExecutionRows (HostFinalMemory.baseWitness (HostObserved.baseWitness witness))
    Multiset.filter (fun msg => MemoryMsg.locOf msg = loc)
        (↑((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (LocalCore.sourceWitness core)) : Multiset _) +
      pushesAt rows loc + Multiset.filter (fun msg => MemoryMsg.locOf msg = loc)
        (↑((LocalCore.memoryRefreshes core).map Prod.snd) : Multiset _) =
    Multiset.filter (fun msg => MemoryMsg.locOf msg = loc)
        (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness core)) : Multiset _) +
      pullsAt rows loc + Multiset.filter (fun msg => MemoryMsg.locOf msg = loc)
        (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _) := by
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  have physical := HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)
  have projected : (hostWitness witness).BalancedChannel memoryChannel.toRaw := by
    change BalancedInteractions ((hostWitness witness).interactionsWith memoryChannel.toRaw)
    rwa [host_protocol_ledger witness _ (by simp)]
  exact source_execution_memory_balance boundary physical projected
    (words_partition witness checked packet installed packetChecked balanced cursor wordData bytes ordering _ _ (.refl _)) loc

/-- The same conservation law has single-record endpoints. Private ordering and fixed
membership ledgers authenticate uniqueness on both sides of each location's history. -/
theorem execution_memory_frontier (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw)
    (boundaries : ∀ channel ∈ (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel) (loc : MemLoc) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let rows := sourceExecutionRows (HostFinalMemory.baseWitness (HostObserved.baseWitness witness))
    optMS (LocalCore.memoryInitialFrontier core loc) + pushesAt rows loc +
        Multiset.filter (fun msg => MemoryMsg.locOf msg = loc) (↑((LocalCore.memoryRefreshes core).map Prod.snd) : Multiset _) =
      optMS (LocalCore.memoryFinalFrontier core loc) + pullsAt rows loc +
        Multiset.filter (fun msg => MemoryMsg.locOf msg = loc) (↑((LocalCore.memoryRefreshes core).map Prod.fst) : Multiset _) := by
  intro core rows
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
  have physical := HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)
  have project (ch : RawChannel Fp) (original : ch ∈ (LocalCore.baseEnsemble image source).channels)
      (funded : witness.BalancedChannel ch) : (hostWitness witness).BalancedChannel ch := by
    change BalancedInteractions ((hostWitness witness).interactionsWith ch)
    rwa [host_core_ledger witness ch original]
  have frontier := HostHintReadLocal.source_memory_frontier_balance boundary physical ordering.byte
    (project _ (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels]) memory)
    (project _ (by simp [LocalCore.baseEnsemble]) (boundaries _ (List.mem_cons_self ..)))
    (project _ (by simp [LocalCore.baseEnsemble]) (boundaries _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (fun ch member => project ch (by
      simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [LocalCore.baseEnsemble])
      (boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))) loc
  have groups := words_partition witness checked packet installed packetChecked balanced cursor wordData bytes ordering
    boundary.data (LocalCore.executionRows core) (.refl _)
  have ledger := source_execution_memory_projection boundary physical groups loc
  rw [add_assoc, add_assoc]
  exact (congrArg (optMS (LocalCore.memoryInitialFrontier core loc) + ·) ledger.1).trans
    (frontier.trans (congrArg (optMS (LocalCore.memoryFinalFrontier core loc) + ·) ledger.2.symm))

end SP1Clean.Export.WriteSourceRegistry
