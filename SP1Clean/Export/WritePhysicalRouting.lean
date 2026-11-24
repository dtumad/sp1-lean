import SP1Clean.Export.WritePhysicalWords
import SP1Clean.Proofs.Completeness.WriteSourceCoverage

/-! # Native probe coverage for all occupied CPU cuts

One actual Memory replay is fixed for each location. For every physical CPU event and
legal x12 or aligned guest-RAM address, the complete original inventory contains a
live receipt accepted by the native probe for the exact replayed 64-bit word.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory
open TraceGen.MemoryHistoryAccess (heldAt ofRecords)

private abbrev Fp := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

/-- The original CPU, HINT_READ, refresh and finalizer tables fund an accepted native
read of the unique chronological word at every occupied, legal incoming CPU cut. -/
theorem routable_physical_cuts (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
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
      ∀ loc,
        let entries := MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned additional (LocalCore.memoryRefreshes core))
        (LocalCore.memoryInitialFrontier core loc = none ∧ LocalCore.memoryFinalFrontier core loc = none ∧ entries = []) ∨
          ∃ first last path, LocalCore.memoryInitialFrontier core loc = some first ∧ LocalCore.memoryFinalFrontier core loc = some last ∧
            locContent source.sail.realize loc = some first.value.toBitVec64 ∧ path.Perm entries ∧ Walk.IsWalk id first last path ∧
            (path.map (fun e => MemoryMsg.timeNat e.2)).Pairwise (· < ·) ∧
            ∀ event ∈ cpu, ValidKey loc.busAddress →
              let time := StateMsg.timeNat (event.edge boundary.data).1
              let word := Target.bitVecToWord (heldAt first.value.toBitVec64 time (path.map ofRecords))
              ∃ r ∈ Counted.live (records (raw witness)), Counted.Covers r ⟨Address.ofNat loc.busAddress, Address.ofNat time, word⟩ := by
  intro core boundary cpu words extra
  obtain ⟨aligned, paired, histories⟩ := physical_coverage_at_cuts valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  have bounds := live_records_bounded valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program
    (fun ch inside => boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inside)))
  have keys := live_keys_canonical valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  have wordsOK := live_words_canonical valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  refine ⟨aligned, paired, fun loc => ?_⟩
  obtain ⟨history, funding⟩ := histories loc
  rcases history with ⟨empty, stopped, clear, _⟩ | ⟨first, last, path, start, finish, sourceWord, perm, walk, ordered, values⟩
  · exact Or.inl ⟨empty, stopped, clear⟩
  refine Or.inr ⟨first, last, path, start, finish, sourceWord, perm, walk, ordered, fun event active legal => ?_⟩
  let time := StateMsg.timeNat (event.edge boundary.data).1
  obtain ⟨r, receipt, live, query⟩ := funding first start event active
  have key := keys r live
  have canonical := wordsOK r live
  have bounded := bounds r live
  have address : Address.toNat r.key = loc.busAddress := key.2.trans (congrArg MemLoc.busAddress receipt.2.1)
  have clockBound : time < 2 ^ 48 := by
    have horizon := receipt.2.2.2
    have hi := bounded.2.2.1
    have lo := bounded.2.2.2
    change time ≤ clkNat r.currentHigh r.currentLow at horizon
    unfold clkNat at horizon
    omega
  have value : Target.bitVecToWord (heldAt first.value.toBitVec64 time (path.map ofRecords)) = r.value :=
    Word.eq_of_toBitVec64_eq (Target.isU64_bitVecToWord _) canonical ((Target.toBitVec64_bitVecToWord _).trans (values time _ query))
  refine ⟨r, live, ?_⟩
  rw [← address, Address.ofNat_toNat key.1, value]
  exact Counted.covers_record r bounded key.1 (address ▸ legal) canonical time clockBound receipt.2.2

end SP1Clean.Export.WriteSourceRegistry
