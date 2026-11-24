import SP1Clean.Export.WritePhysicalCoverage

/-! # Canonical addresses throughout the physical Memory replay

The actual access pairs retain the original three address fields. Starting at the
authenticated Sail snapshot therefore fixes the raw key of every later record,
including host RAM writes, intermediate aliases, refreshes and finalizers.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
private abbrev Pair := MemoryRecordChain.Pair SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem address_canonical {a b : MemoryMsg Fp} (equal : MemoryBoundary.address a = MemoryBoundary.address b)
    (before : MemoryBoundary.CanonicalSpec a) : MemoryBoundary.CanonicalSpec b := by
  have same (i : Fin 4) := congrArg (fun w : Word Fp => w[i]) equal
  have zero : a.addr0 = b.addr0 := same 0
  have one : a.addr1 = b.addr1 := same 1
  have two : a.addr2 = b.addr2 := same 2
  have loc : MemoryMsg.locOf a = MemoryMsg.locOf b := by simp only [MemoryMsg.locOf, zero, one, two]
  exact ⟨loc ▸ before.1, equal ▸ before.2.1, (congrArg Word.toNat equal).symm.trans (before.2.2.trans (congrArg MemLoc.busAddress loc))⟩

private theorem canonical_path {first last : MemoryMsg Fp} {path : List Pair} (walk : Walk.IsWalk id first last path)
    (canonical : MemoryBoundary.CanonicalSpec first) (retain : ∀ e ∈ path, MemoryBoundary.address e.1 = MemoryBoundary.address e.2) :
    ∀ e ∈ path, MemoryBoundary.CanonicalSpec e.1 ∧ MemoryBoundary.CanonicalSpec e.2 := by
  induction path generalizing first with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨rfl, rest⟩ := walk
    have next := address_canonical (retain head (List.mem_cons_self ..)) canonical
    intro e member
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨canonical, next⟩
    · exact ih rest next (fun other h => retain other (List.mem_cons_of_mem _ h)) e inside

private theorem all_addresses (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (data : ProverData Fp) (words : List (HintReadCoverage.Row (p := SP1Prime))) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows core).map (ExecutionRow.facts data))) :
    let extra := ((LocalCore.executionRows core).flatMap (wordsAt data words)).map touch
    ∀ edge ∈ MemoryRecordChain.pairs aligned extra (LocalCore.memoryRefreshes core),
      MemoryBoundary.address edge.1 = MemoryBoundary.address edge.2 := by
  intro extra e member
  rcases List.mem_append.mp member with executed | bumped
  · obtain ⟨t, inside, rfl⟩ := List.mem_map.mp executed
    rcases List.mem_append.mp inside with original | host
    · obtain ⟨r, present, slot⟩ := List.mem_flatMap.mp original
      obtain ⟨_, _, facts⟩ := forall₂_exists_right paired r present
      exact facts.addresses t slot
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp host
      rfl
  · obtain ⟨row, _, h⟩ := List.mem_flatMap.mp bumped
    obtain rfl := List.mem_singleton.mp h
    rfl

/-- A physical key is the exact canonical three-field encoding of its decoded location. -/
def CanonicalReceiptKey (r : Readback Fp) : Prop :=
  Address.Bounded r.key ∧ Address.toNat r.key = (keyLocation r.key).busAddress

private theorem canonical_key (prior : MemoryMsg Fp) (r : Readback Fp)
    (key : r.key = #v[prior.addr0, prior.addr1, prior.addr2]) (canon : MemoryBoundary.CanonicalSpec prior) : CanonicalReceiptKey r := by
  have address : Word.toNat (Address.asWord r.key) = (keyLocation r.key).busAddress := by rw [key]; exact canon.2.2
  exact ⟨Address.bounded_of_isU64_asWord (key ▸ canon.2.1), (Address.toNat_asWord r.key).symm.trans address⟩

/-- A live registry occurrence agrees field-for-field with an actual predecessor or
terminal record of this original physical history. -/
theorem physical_representative (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (data : ProverData Fp) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness witness))).map (ExecutionRow.facts data)))
    (r : Readback Fp) (live : r ∈ Counted.live (records (raw witness))) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
    let extra := ((LocalCore.executionRows core).flatMap (wordsAt data words)).map touch
    ∃ prior : MemoryMsg Fp, r.key = #v[prior.addr0, prior.addr1, prior.addr2] ∧ r.value = prior.value ∧
      ((∃ next, (prior, next) ∈ MemoryRecordChain.pairs aligned extra (LocalCore.memoryRefreshes core)) ∨
        prior ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness core)) := by
  intro core words extra
  obtain ⟨occurrence, member, rfl⟩ := List.mem_map.mp live
  obtain ⟨signed, gate⟩ := List.mem_filter.mp member
  obtain ⟨id, origin⟩ := origin_of_record _ (raw_registered witness) signed ((of_decide_eq_true gate).trans_ne one_ne_zero)
  rcases source_attribution witness checked packet installed packetChecked balanced cursor wordData bytes id occurrence.2 origin with
    ⟨event, present, prior, micro, pulled, eq⟩ | ⟨prior, next, present, eq⟩ | ⟨prior, present, eq⟩
  · rw [eventFacts_setData event core.data data words] at pulled
    obtain ⟨next, edge, _⟩ := paired_predecessor data _ words aligned paired (word_access witness checked bytes) _ present pulled
    exact ⟨prior, congrArg Readback.key eq, congrArg Readback.value eq, Or.inl ⟨next, edge⟩⟩
  · exact ⟨prior, congrArg Readback.key eq, congrArg Readback.value eq, Or.inl ⟨next, List.mem_append_right _ present⟩⟩
  · exact ⟨prior, congrArg Readback.key eq, congrArg Readback.value eq, Or.inr present⟩

/-- Every live original readback carries the exact address limbs of its canonical
location. This fact follows even for Memory pulls from register aliases and RAM writes. -/
theorem live_keys_canonical (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
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
    ∀ record ∈ Counted.live (records (raw witness)), CanonicalReceiptKey record := by
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
  let edges := MemoryRecordChain.pairs aligned extra (LocalCore.memoryRefreshes core)
  have all := all_addresses core boundary.data words aligned paired
  have canon {e : Pair} (active : e ∈ edges) : MemoryBoundary.CanonicalSpec e.1 := by
    let loc := MemoryMsg.locOf e.2
    have atLoc : e ∈ MemoryRecordChain.atLocation loc edges := List.mem_filter.mpr ⟨active, by simp [loc]⟩
    rcases histories loc with ⟨_, _, empty⟩ | ⟨first, last, path, start, _, perm, walk, _, _⟩
    · exact (List.not_mem_nil (empty ▸ atLoc)).elim
    have seed := (LocalCore.memoryInitialFrontier_content_of_channels core physical ordering.sourceChecks ordering.byte membership start).2.1.canonical
    exact (canonical_path walk seed (fun e member => all e (List.mem_filter.mp (perm.mem_iff.mp member)).1) e (perm.mem_iff.mpr atLoc)).1
  intro record live
  obtain ⟨prior, key, _, physicalSource⟩ := physical_representative witness checked packet installed packetChecked balanced cursor wordData bytes boundary.data aligned paired record live
  apply canonical_key prior record key
  rcases physicalSource with ⟨next, member⟩ | present
  · exact canon (e := (prior, next)) member
  · have hostChecked := HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked))
    have finalOrder : (hostWitness witness).BalancedChannel (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
      change BalancedInteractions ((hostWitness witness).interactionsWith _)
      rw [host_core_ledger witness _ (by simp [LocalCore.baseEnsemble])]
      exact boundaries _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have terminal := (HostLocalCore.final_records_canonical_nodup (hostWitness witness)
      (HostHintReadLocal.source_boundary_silent source _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hostChecked ordering.byte finalOrder).1 prior present
    exact terminal

end SP1Clean.Export.WriteSourceRegistry
