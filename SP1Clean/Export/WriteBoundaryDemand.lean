import SP1Clean.Export.WriteBoundaryBuild
import SP1Clean.Proofs.Completeness.MixedMemorySelection
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

/-- Every emitted x12 or aligned buffer read equals the canonical field encoding of the word held
by the original mixed Memory stream at that exact WRITE's incoming clock. -/
theorem readDemand_heldAt {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets)) :
    ∃ call loc, events[cut]? = some (.syscall call) ∧ call.rawCode = SyscallKind.write.code ∧ ValidKey loc.busAddress ∧
      read = ⟨Address.ofNat loc.busAddress, Address.ofNat call.clock, Target.bitVecToWord
        (MemoryHistoryAccess.heldAt (source.sail.memorySnapshot.read loc) call.clock
          (memoryHistoryAt (MixedMemoryHistory.stream image source events rows) loc))⟩ := by
  obtain ⟨call, current, frontier, loc, present, write, time, atCut, legal, key, clock, bounded, observed⟩ :=
    readDemand_at run collected member
  have word := MixedMemoryHistory.heldAt_cut run routed atCut loc (valid_location loc legal)
  refine ⟨call, loc, present, write, legal, ?_⟩
  rw [time]
  have encoded := Word.eq_of_toBitVec64_eq bounded (Target.isU64_bitVecToWord _)
    ((Option.some.inj (observed.symm.trans word)).trans (Target.toBitVec64_bitVecToWord _).symm)
  cases read
  congr

/-- Every actual read at a fresh boundary key either has a previous compiler access at the cut
or is covered by a positive record from the compiled register or RAM finalizer. -/
private theorem readDemand_sparse_source {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    {limits : ResourceLimits} (run : AdmissibleExecution limits SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (stream : List MemoryHistoryAccess) (canonical : MemoryAddressesCanonical stream)
    (fresh : Address.toNat read.key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (data : ProverData F) (hint : ProverHint F) (raw : AccessInventory.Source → Table F)
    (installed : FinalRows raw source.sail.memorySnapshot stream (demandKeys events packets) canonical data hint) :
    ∃ current frontier loc, mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier) ∧
      loc.busAddress = Address.toNat read.key ∧ read.clock = Address.ofNat current.clock ∧
      (0 < frontier loc ∨ ∃ record ∈ Counted.live (AccessInventory.records raw), Counted.Covers record read) := by
  obtain ⟨_, current, frontier, loc, _, _, _, atCut, legal, key, clock, bounded, observed⟩ := readDemand_at run collected member
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
    obtain ⟨other, matchKey, record, live, covers⟩ := sparse_live_covers_of_rows raw source.sail.memorySnapshot stream (demandKeys events packets) data hint _ installed loc.busAddress wanted legal (keyNat ▸ fresh) current.clock (by omega)
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
private theorem sparse_read_of_rows {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {rows : List MixedCompiledRow} (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (fresh : Address.toNat read.key ∉ (memoryInitialEntries (MixedMemoryHistory.stream image source events rows)).map MemRecordEntry.addr)
    (data : ProverData F) (hint : ProverHint F) (raw : AccessInventory.Source → Table F)
    (installed : FinalRows raw source.sail.memorySnapshot _ (demandKeys events packets) (MixedMemoryHistory.canonical run routed) data hint) :
    ∃ record ∈ Counted.live (AccessInventory.records raw), Counted.Covers record read := by
  obtain ⟨current, frontier, loc, before, key, _, posted | covered⟩ := readDemand_sparse_source run collected member
    _ (MixedMemoryHistory.canonical run routed) fresh data hint raw installed
  · have absent : loc ∉ touchedMemoryLocations (MixedMemoryHistory.stream image source events rows) := by
      intro found
      rw [memoryInitialEntries_addresses] at fresh
      exact fresh (List.mem_map.mpr ⟨loc, found, key⟩)
    have zero := MixedMemoryHistory.zero_of_absent run routed absent before
    omega
  · exact covered

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
    ∃ record ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers record read :=
  sparse_read_of_rows run collected routed member fresh data hint _ (finalizer_rows image source target endQueue _ _
    (MixedMemoryHistory.canonical run routed) data hint header suffix registered)

/-- The original mixed table occurrence which will supply a packet read before its event
replaces that word. The bounds use the displaced record time and its true incoming CPU clock. -/
def CompiledPredecessor (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (rows : List MixedCompiledRow) (cut : ℕ) (read : Read F) : Prop :=
  ∃ (i : Fin rows.length) (before : ExecutionState) (a : MemoryHistoryAccess) (call : CoreSyscallEvent),
      events[cut]? = some (.syscall call) ∧ call.rawCode = SyscallKind.write.code ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events i.val = some before ∧
      a ∈ MixedMemoryHistory.batch image source events rows i ∧ ValidKey a.loc.busAddress ∧
      a.previous ≤ call.clock ∧ call.clock ≤ before.clock ∧ before.clock < 2 ^ 48 ∧
      read = ⟨Address.ofNat a.loc.busAddress, Address.ofNat call.clock, Target.bitVecToWord a.pulled⟩

/-- Each read of each actual WRITE is already funded by a live installed finalizer, or it is
precisely the prior word of an actual compiled row at a clock covered by that row. This includes
both the otherwise untouched case and exhaustion of a nonempty Memory history. -/
theorem read_source_of_rows {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (data : ProverData F) (hint : ProverHint F) (raw : AccessInventory.Source → Table F)
    (installed : FinalRows raw source.sail.memorySnapshot _ (demandKeys events packets) (MixedMemoryHistory.canonical run routed) data hint) :
    (∃ r ∈ Counted.live (AccessInventory.records raw), Counted.Covers r read) ∨
    CompiledPredecessor image source events rows cut read := by
  let tape := MixedMemoryHistory.stream image source events rows
  by_cases occupied : Address.toNat read.key ∈ (memoryInitialEntries tape).map MemRecordEntry.addr
  swap
  · exact Or.inl (sparse_read_of_rows run collected routed member occupied data hint raw installed)
  obtain ⟨call, current, frontier, loc, present, write, atTime, atCut, legal, key, clock, bounded, observed⟩ := readDemand_at run collected member
  have canonical := valid_location loc legal
  have keyNat : Address.toNat read.key = loc.busAddress := by rw [key, Address.toNat_ofNat _ (MemLoc.busAddress_lt_two_pow_48 canonical)]
  rw [memoryInitialEntries_addresses, keyNat] at occupied
  obtain ⟨other, used, equal⟩ := List.mem_map.mp occupied
  obtain ⟨r, inTape, whereAt⟩ := mem_touchedMemoryLocations.mp used
  have locEq := MemLoc.busAddress_injective_of_canonical (whereAt ▸ MixedMemoryHistory.canonical run routed r inTape) canonical equal
  have touched : loc ∈ touchedMemoryLocations tape := locEq ▸ used
  have encoded (v : BitVec 64) (held : locContent current.sail loc = some v) :
      read = ⟨Address.ofNat loc.busAddress, Address.ofNat current.clock, Target.bitVecToWord v⟩ := by
    have value := Word.eq_of_toBitVec64_eq bounded (Target.isU64_bitVecToWord _)
      ((Option.some.inj (observed.symm.trans held)).trans (Target.toBitVec64_bitVecToWord _).symm)
    cases read
    congr
  rcases MixedMemoryHistory.select_at_cut run routed atCut loc touched with later | finished
  · obtain ⟨i, before, a, prior, listed, same, lower, upper, fits, word⟩ := later
    exact Or.inr ⟨i, before, a, call, present, write, prior, listed, same ▸ legal, atTime ▸ lower, atTime ▸ upper,
      fits, by rw [same, atTime]; exact encoded _ word⟩
  · obtain ⟨history, listed, same, prior, word⟩ := finished
    obtain ⟨state, f, path, reached, _⟩ := admissibleExecution_mixedAccessPrefix run cut
    cases Option.some.inj (atCut.symm.trans reached)
    have final := run.1.2.clock_at present path
    change current.clock + _ ≤ target.clock at final
    have limit : target.clock < 2 ^ 48 := run.2.2.2.2.2.1
    obtain ⟨record, live, cover⟩ := terminal_covers_of_rows raw source.sail.memorySnapshot tape (demandKeys events packets)
      (MixedMemoryHistory.canonical run routed) data hint installed history listed (same ▸ legal)
      current.clock prior (by omega)
    rw [same] at cover
    exact Or.inl ⟨record, live, encoded _ word ▸ cover⟩

/-- The registered finalizers and mixed rows of the assembled supervisor supply the actual packet read. -/
theorem compiled_read_source {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets))
    (endQueue : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F)
    (suffix : List (Table F)) (registered) :
    let stream := MixedMemoryHistory.stream image source events rows
    let w := build image source target endQueue stream (demandKeys events packets) (MixedMemoryHistory.canonical run routed)
      data hint header suffix registered
    (∃ r ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers r read) ∨
    CompiledPredecessor image source events rows cut read :=
  read_source_of_rows run collected routed member data hint _ (finalizer_rows image source target endQueue _ _
    (MixedMemoryHistory.canonical run routed) data hint header suffix registered)

/-- One native execution generates its original six Memory boundary tables and all packet reads.
The six tables meet their actual component constraints and channel guarantees. Every read is
funded at a registered finalizer or identifies the original mixed row which displaced its word. -/
theorem sources_of_admissibleExecution {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    ∃ packets rows, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      ∃ routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows,
        let stream := MixedMemoryHistory.stream image source events rows
        let requested := demandKeys events packets
        (∀ data hint t, t ∈ boundaryTables source.sail.memorySnapshot stream requested (MixedMemoryHistory.canonical run routed) data hint →
          t.Constraints ∧ t.Guarantees) ∧
        ∀ endQueue data hint header suffix registered,
          let w := build image source target endQueue stream requested (MixedMemoryHistory.canonical run routed)
            data hint header suffix registered
          ∀ cut read, (cut, read) ∈ readDemand (packetRows events packets) →
            (∃ record ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)), Counted.Covers record read) ∨
            CompiledPredecessor image source events rows cut read := by
  obtain ⟨packets, collected⟩ := WriteObservations.admissible_packets run
  obtain ⟨rows, routed, _⟩ := admissibleExecution_routeMixedRows run
  refine ⟨packets, rows, collected, routed, ?_, fun endQueue data hint header suffix registered _ _ member =>
    compiled_read_source run collected routed member endQueue data hint header suffix registered⟩
  exact fun data hint => boundaryTables_valid _ _ _ (MixedMemoryHistory.addresses_in_layout run routed) data hint

end SP1Clean.Export.WriteBoundaryBuild
