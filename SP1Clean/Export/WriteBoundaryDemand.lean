import SP1Clean.Export.WriteBoundaryBuild
import SP1Clean.Proofs.Completeness.MixedMemoryHistory
import SP1Clean.Proofs.Completeness.UntouchedMemory
import SP1Clean.Proofs.Completeness.WriteBufferBatch

/-! # Funding actual WRITE requests from the authenticated source snapshot

The chronological packet collector provides the keys for the sparse boundary constructor.
An untouched register or RAM cell keeps its incoming value throughout the semantic prefix,
including ordinary register writeback and the full padded HINT_READ span. The two registered
Memory finalizers therefore cover the actual read, with the same field limbs and the same clock.
-/

namespace SP1Clean.Export.WriteBoundaryBuild

open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen Soundness WriteProbe WriteBuffer WriteProbe.SparseBoundary

private abbrev F := ZMod SP1Prime

/-- Every repeated x12 and word request is passed to the sparse compiler in tape order.
The boundary's existing ordered key inventory performs the physical deduplication. -/
def demandKeys (events : List ExecutionEvent) (packets : List WriteObservations.Packet) : List ℕ :=
  (readDemand (packetRows (p := SP1Prime) events packets)).map fun entry => Address.toNat entry.2.key

private theorem valid_location (loc : MemLoc) (legal : ValidKey loc.busAddress) : loc.CanonicalAddress := by
  cases loc with
  | reg => trivial
  | ram cell =>
    change cell.toNat * 8 = 12 ∨ _ at legal
    change 32 ≤ cell.toNat * 8 ∧ cell.toNat * 8 < 2 ^ 48
    rcases legal with equal | ⟨lower, upper, _⟩
    · omega
    · exact ⟨by change 2 ^ 16 ≤ cell.toNat * 8 at lower; omega, upper⟩

/-- Every actual read at a fresh boundary key either has a previous compiler access at the cut
or is covered by a positive physical finalizer. The witness is the canonical original supervisor
containing the compiler's six boundary tables. -/
private theorem readDemand_sparse_source {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    {limits : ResourceLimits} (run : AdmissibleExecution limits SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (endQueue : HostHintQueue.State F) (stream : List MemoryHistoryAccess) (canonical : MemoryAddressesCanonical stream)
    (fresh : Address.toNat read.key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered) :
    let w := build image source target endQueue stream (demandKeys events packets) canonical data hint header suffix registered
    ∃ current frontier loc, mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier) ∧
      loc.busAddress = Address.toNat read.key ∧ read.clock = Address.ofNat current.clock ∧
      (0 < frontier loc ∨ ∃ record ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers record read) := by
  obtain ⟨current, frontier, loc, atCut, legal, key, clock, bounded, observed⟩ := readDemand_at run collected member
  have location := valid_location loc legal
  have keyNat : Address.toNat read.key = loc.busAddress := by
    rw [key, Address.toNat_ofNat _ (MemLoc.busAddress_lt_two_pow_48 location)]
  refine ⟨current, frontier, loc, atCut, keyNat.symm, clock, ?_⟩
  by_cases zero : frontier loc = 0
  · right
    have framed := admissibleExecution_untouched run atCut loc zero
    have snapshot := run.1.1.memory.locContent loc location
    have word : read.value = Target.bitVecToWord (source.sail.memorySnapshot.read loc) :=
      Word.eq_of_toBitVec64_eq bounded (Target.isU64_bitVecToWord _) ((Option.some.inj
        (observed.symm.trans (framed.trans snapshot))).trans (Target.toBitVec64_bitVecToWord _).symm)
    obtain ⟨seen, old, replay, atCut', _⟩ := admissibleExecution_mixedAccessPrefix run cut
    cases Option.some.inj (atCut'.symm.trans atCut)
    obtain ⟨middle, left, right⟩ := run.1.2.split cut
    have currentEq : middle = current := Option.some.inj (left.replay.symm.trans replay)
    have time := right.clock
    rw [currentEq] at time
    have final : target.clock < 2 ^ 48 := run.2.2.2.2.2.1
    change target.clock = current.clock + _ at time
    have wanted : loc.busAddress ∈ demandKeys events packets := List.mem_map.mpr ⟨(cut, read), member, keyNat⟩
    obtain ⟨other, matchKey, record, live, covers⟩ := build_sparse_covers image source target endQueue stream (demandKeys events packets)
      canonical data hint header suffix registered loc.busAddress wanted legal (keyNat ▸ fresh) current.clock (by omega)
    have sameLoc := MemLoc.busAddress_injective_of_canonical (valid_location other (matchKey.symm ▸ legal)) location matchKey
    rw [sameLoc] at covers
    refine ⟨record, live, ?_⟩
    have same : read = ⟨Address.ofNat loc.busAddress, Address.ofNat current.clock, Target.bitVecToWord (source.sail.memorySnapshot.read loc)⟩ := by
      cases read
      congr
    exact same.symm ▸ covers
  · exact Or.inl (Nat.pos_of_ne_zero zero)

/-- A real WRITE request for a key absent from the complete mixed access stream is funded at its
actual tape cut. Key absence itself implies clock zero on the mixed compiler frontier. -/
theorem compiled_sparse_read {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {rows : List MixedCompiledRow} (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (endQueue : HostHintQueue.State F)
    (fresh : Address.toNat read.key ∉ (memoryInitialEntries (MixedMemoryHistory.stream image source events rows)).map MemRecordEntry.addr)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered) :
    let w := build image source target endQueue (MixedMemoryHistory.stream image source events rows) (demandKeys events packets) (MixedMemoryHistory.canonical run routed)
      data hint header suffix registered
    ∃ record ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers record read := by
  obtain ⟨current, frontier, loc, before, key, _, posted | covered⟩ := readDemand_sparse_source run collected member
    endQueue _ (MixedMemoryHistory.canonical run routed) fresh data hint header suffix registered
  · have absent : loc ∉ touchedMemoryLocations (MixedMemoryHistory.stream image source events rows) := by
      intro found
      rw [memoryInitialEntries_addresses] at fresh
      exact fresh (List.mem_map.mpr ⟨loc, found, key⟩)
    have zero := MixedMemoryHistory.zero_of_absent run routed absent before
    omega
  · exact covered

/-- One admissible mixed execution generates both source and demand inventories. Every otherwise
untouched request is funded on each canonical supervisor built with their six registered boundary tables. -/
theorem sparse_suppliers_of_admissibleExecution {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    ∃ packets rows, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      ∃ routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows,
        let stream := MixedMemoryHistory.stream image source events rows
        ∀ endQueue data hint header suffix registered,
          let w := build image source target endQueue stream (demandKeys events packets) (MixedMemoryHistory.canonical run routed)
            data hint header suffix registered
          ∀ cut read, (cut, read) ∈ readDemand (packetRows events packets) →
            Address.toNat read.key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr →
              ∃ record ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers record read := by
  obtain ⟨packets, collected⟩ := WriteObservations.admissible_packets run
  obtain ⟨rows, routed, _⟩ := admissibleExecution_routeMixedRows run
  exact ⟨packets, rows, collected, routed, fun endQueue data hint header suffix registered _ _ member fresh =>
    compiled_sparse_read run collected routed member endQueue fresh data hint header suffix registered⟩

end SP1Clean.Export.WriteBoundaryBuild
