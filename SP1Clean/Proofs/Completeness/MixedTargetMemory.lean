import SP1Clean.Proofs.Completeness.MixedMemoryRecords
import SP1Clean.Proofs.Completeness.WriteSparseMemory
import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.Native.Operations.FinalRegisterCheck
import SP1Clean.Native.Operations.FinalRamCheck

/-! # Authenticating every generated finalizer against the outgoing Sail snapshot

An occupied location carries the last word of its genuine mixed transfer chain. An additional
WRITE observation at an untouched location retains the original source word. Both branches
supply the original target register or eight-byte RAM checker at the actual boundary record.
-/

namespace SP1Clean.TraceGen.MixedTargetMemory

open Circuit Air.Flat Semantics Soundness Machine FormalModel.Shard Channels
open WriteProbe.SparseBoundary

private abbrev F := ZMod SP1Prime

private theorem sparse_word (snapshot : MemorySnapshot) (tape : List MemoryHistoryAccess) (keys : List ℕ)
    (data : ProverData F) (hint : ProverHint F) {extra : Rows F}
    (member : extra ∈ buildAll snapshot ((memoryInitialEntries tape).map MemRecordEntry.addr) keys data hint) :
    let record := (terminalOfRows snapshot data extra).record
    MemoryMsg.locOf record ∉ touchedMemoryLocations tape ∧
      Word.toBitVec64 record.value = snapshot.read (MemoryMsg.locOf record) := by
  obtain ⟨i,fresh,built⟩ := (mem_buildAll_iff ..).mp member
  obtain ⟨actual,also,key,checked⟩ := build?_checked snapshot _ keys i fresh data hint
  obtain rfl := Option.some.inj (also.symm.trans built)
  let record := (terminalOfRows snapshot data actual).record
  have authentic : MemoryBoundary.SnapshotAtSpec snapshot actual.key record := checked.2.2.1
  refine ⟨?_,authentic.1.2.2.2.2.1.symm⟩
  intro occupied
  have usedKey : (MemoryMsg.locOf record).busAddress ∈ (touchedMemoryLocations tape).map MemoryHistoryAccess.busAddress :=
    List.mem_map_of_mem occupied
  rw [← memoryInitialEntries_addresses, ← authentic.1.canonical.2.2, authentic.2, key] at usedKey
  exact fresh usedKey

private theorem all_words (source target : MemorySnapshot) (tape : List MemoryHistoryAccess) (keys : List ℕ)
    (data : ProverData F) (hint : ProverHint F) (guest : MemoryAddressesInLayout tape)
    {initial final : AccessFrontier} {incoming outgoing : LocationValues}
    (transfers : MemoryHistoryAccess.Transfers initial final incoming outgoing tape)
    (sourceAt : ∀ loc, loc.CanonicalAddress → incoming loc = some (source.read loc))
    (targetAt : ∀ loc, loc.CanonicalAddress → outgoing loc = some (target.read loc))
    {r : Terminal F} (used : r ∈ terminals source tape keys data hint) :
    Word.toBitVec64 r.record.value = target.read (MemoryMsg.locOf r.record) := by
  have valid := terminals_valid source tape keys guest data hint r used
  have address := valid.canonical
  apply Option.some.inj
  apply Eq.trans _ (targetAt _ address.1)
  rcases List.mem_append.mp (List.mem_mergeSort.mp used) with touched | spare
  · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp touched
    obtain ⟨h,atHistory,rfl⟩ := List.mem_map.mp atEntry
    have present : h.loc ∈ touchedMemoryLocations tape := memoryLocationHistories_map_loc tape ▸ List.mem_map_of_mem (f := MemoryLocationHistory.loc) atHistory
    have same := MemLoc.busAddress_injective_of_canonical address.1 (canonical_of_mem_touched guest.canonical present)
      (address.2.2.symm.trans valid.1)
    rw [same]
    change some (Word.toBitVec64 (wordOfNat h.last.pushed.toNat)) = _
    rw [toBitVec64_wordOfNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact transfers.final_word atHistory
  · obtain ⟨extra,atExtra,rfl⟩ := List.mem_map.mp spare
    obtain ⟨fresh,word⟩ := sparse_word source tape keys data hint atExtra
    exact (congrArg some word).trans ((sourceAt _ address.1).symm.trans (transfers.untouched_word fresh))

private theorem outgoing_memory (snapshot : SailSnapshot) (initialized : snapshot.realize.isInitialized) :
    snapshot.memorySnapshot.Realizes snapshot.realize :=
  snapshot.memorySnapshot_realizes (fun reg => initialized reg)

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (keys : List ℕ) (data : ProverData F) (hint : ProverHint F)

include run routed

/-- Every actual terminal word, including the extra untouched WRITE locations, agrees with the
complete outgoing Sail snapshot. -/
theorem terminal_word {r : Terminal F} (used : r ∈ terminals source.sail.memorySnapshot (MixedMemoryHistory.stream image source events rows) keys data hint) :
    Word.toBitVec64 r.record.value = target.sail.memorySnapshot.read (MemoryMsg.locOf r.record) := by
  obtain ⟨_,_,transfers,_⟩ := MixedMemoryHistory.records run routed
  exact all_words _ _ _ keys data hint (MixedMemoryHistory.addresses_in_layout run routed) transfers
    run.1.1.memory.locContent (outgoing_memory target.sail run.1.frame.1.init).locContent used

/-- Both actual native target-value checks accept their own register or aligned RAM finalizer. -/
theorem terminal_spec {r : Terminal F} (used : r ∈ terminals source.sail.memorySnapshot (MixedMemoryHistory.stream image source events rows) keys data hint) :
    if r.ram then FinalRamValue.Spec target.sail.memorySnapshot r.record
    else FinalRegisterValue.Spec target.sail.memorySnapshot r.record := by
  have guest := MixedMemoryHistory.addresses_in_layout run routed
  have valid := terminals_valid source.sail.memorySnapshot _ keys guest data hint r used
  have value := terminal_word run routed keys data hint used
  have domain := valid.2.2.2
  cases tag : r.ram <;> rw [tag] at domain
  · change FinalRegisterProvider.Domain r.record at domain
    exact ⟨domain.1,domain.2.1,domain.2.2,valid.2.1,value⟩
  · change FinalRamProvider.Domain r.record at domain
    have bounded := valid.canonical.2.2
    have lower := domain.2.1
    have upper := domain.2.2.1
    have aligned := domain.2.2.2
    rw [target.sail.memorySnapshot.read_of_ram_address _ (by omega), ← bounded] at value
    exact ⟨domain.1,by omega,valid.2.1,value⟩

end SP1Clean.TraceGen.MixedTargetMemory
