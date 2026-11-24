import SP1Clean.Export.WriteSourceProjection
import SP1Clean.Proofs.Completeness.WriteSparseMemory
import SP1Clean.Proofs.Completeness.WriteSparseOrder
import ToClean.Air.EnsembleBuild

/-! # Installing the compiled Memory boundary in the supervisor

The first six entries are the genuine incoming providers and their terminal, then the
two receipt-publishing finalizers and their terminal. They are installed before the
rest of the genuine supervisor at one shared canonical prover environment.
-/

namespace SP1Clean.Export.WriteBoundaryBuild

open Circuit Air.Flat Semantics TraceGen Soundness WriteProbe WriteProbe.SparseBoundary
open WriteSourceRegistry (base)

private abbrev F := ZMod SP1Prime

/-- The first six committed tables, in the supervisor's physical register/RAM/terminal order. -/
def boundaryTables (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData F) (hint : ProverHint F) : List (Table F) :=
  let rows := terminals snapshot stream requested data hint
  let initial := fun ram => initialTable snapshot ram rows data (terminal_count_fit ram snapshot stream requested canonical data hint)
  let final := fun ram => finalTable ram rows data (terminals_fit ram snapshot stream requested canonical data hint)
  [initial false, initial true, terminalTable SnapshotMemoryEnsemble.channelName (by decide) rows data,
    final false, final true, terminalTable OrderedFinalProvider.channelName (by decide) rows data]

/-- Component identity includes the executable generation mode and the physical input layout. -/
theorem boundaryTables_registered (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream) (data : ProverData F) (hint : ProverHint F) :
    (boundaryTables source.sail.memorySnapshot stream requested canonical data hint).map (·.component) =
      (base image source target endQueue).tables.take 6 := by
  rw [WriteSourceRegistry.boundary_prefix]
  rfl

/-- Every table in the six-slot prefix satisfies its original circuit and channel guarantees. -/
theorem boundaryTables_valid (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : ∀ a ∈ stream, ∀ cell, a.loc = .ram cell → NativeLayout.guestMemory.Contains (MemLoc.ram cell).busAddress)
    (data : ProverData F) (hint : ProverHint F) :
    ∀ t ∈ boundaryTables snapshot stream requested (canonical_addresses guest) data hint, t.Constraints ∧ t.Guarantees := by
  have reg := compiled_boundaries_valid snapshot stream requested guest data hint false
  have ram := compiled_boundaries_valid snapshot stream requested guest data hint true
  have bounded := fun r hr => (terminals_valid snapshot stream requested guest data hint r hr).key_lt
  have start := terminalTable_valid SnapshotMemoryEnsemble.channelName (by decide) _ bounded data
  have finish := terminalTable_valid OrderedFinalProvider.channelName (by decide) _ bounded data
  intro t member
  simp only [boundaryTables, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨reg.1, reg.2.1⟩
  · exact ⟨ram.1, ram.2.1⟩
  · exact start
  · exact ⟨reg.2.2.1, reg.2.2.2.1⟩
  · exact ⟨ram.2.2.1, ram.2.2.2.1⟩
  · exact finish

/-- Install the six compiled providers ahead of the remaining supervisor slots using
Clean's canonical derivation of data from the entire table list. -/
def build (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream) (data : ProverData F)
    (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F))
    (registered : suffix.map (·.component) = (base image source target endQueue).tables.drop 6) :
    EnsembleWitness (base image source target endQueue) :=
  EnsembleWitness.ofTables _ (boundaryTables source.sail.memorySnapshot stream requested canonical data hint ++ suffix) header (by
    rw [List.map_append, boundaryTables_registered image source target endQueue, registered, List.take_append_drop])

/-- The full supervisor's canonical private data preserves every raw occurrence on every
channel in the generated boundary prefix, in the original table and row order. -/
theorem build_prefix_ledger (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream) (data : ProverData F)
    (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered) (ch : RawChannel F) :
    ((build image source target endQueue stream requested canonical data hint header suffix registered).tables.take 6).flatMap (·.interactionsWith ch) =
      (boundaryTables source.sail.memorySnapshot stream requested canonical data hint).flatMap (·.interactionsWith ch) := by
  rw [build, EnsembleWitness.ofTables_tables, withDerivedData_take_interactionsWith]
  let tables := boundaryTables source.sail.memorySnapshot stream requested canonical data hint
  change ((tables ++ suffix).take 6).flatMap _ = tables.flatMap _
  rw [show 6 = tables.length by rfl, List.take_left]

/-- Installing the compiled boundary preserves all local constraints whenever the remaining
physical table constructors supply theirs. -/
theorem build_constraints (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : ∀ a ∈ stream, ∀ cell, a.loc = .ram cell → NativeLayout.guestMemory.Contains (MemLoc.ram cell).busAddress)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered)
    (checked : ∀ t ∈ suffix, t.Constraints) :
    (build image source target endQueue stream requested (canonical_addresses guest) data hint header suffix registered).Constraints := by
  intro t member row included
  have free := HostObserved.lookupFree (image := image) (source := source) (target := target) (final := endQueue)
    t.component (EnsembleWitness.component_mem_tables_of_mem member)
  rw [build, EnsembleWitness.ofTables_tables] at member
  have mapped := List.mem_map_of_mem (f := fun t : Table F => (t.component, t.table)) member
  rw [withDerivedData_map] at mapped
  obtain ⟨old, orig, same⟩ := List.mem_map.mp mapped
  have valid : old.Constraints := by
    rcases List.mem_append.mp orig with first | rest
    · exact (boundaryTables_valid _ _ _ guest _ _ old first).1
    · exact checked old rest
  have eqComponent := congrArg Prod.fst same
  have eqRows := congrArg Prod.snd same
  change old.component = t.component at eqComponent
  change old.table = t.table at eqRows
  exact t.component.constraintsHold_setData free (eqComponent ▸ valid row (eqRows ▸ included))

private theorem finalizer_rows (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered) (ram : Bool) :
    let w := build image source target endQueue stream requested canonical data hint header suffix registered
    let snapshot := source.sail.memorySnapshot
    (WriteSourceRegistry.raw w (.finalizer ram)).table =
      (finalTable ram (terminals snapshot stream requested data hint) data (terminals_fit ram snapshot stream requested canonical data hint)).table := by
  let w := build image source target endQueue stream requested canonical data hint header suffix registered
  let prefixTables := boundaryTables source.sail.memorySnapshot stream requested canonical data hint
  have arrays : w.tables.map (·.table) = (prefixTables ++ suffix).map (·.table) := by
    rw [show w.tables = _ from EnsembleWitness.ofTables_tables .., withDerivedData_map_table]
  let id := AccessInventory.Source.finalizer ram
  let slot := WriteSourceRegistry.originalSlot image source target endQueue id
  have got : w.tables[slot.index.val]? = some (WriteSourceRegistry.raw w id) :=
    List.getElem?_eq_getElem (by rw [← w.same_length]; exact slot.index.isLt)
  have index : slot.index.val = WriteSourceRegistry.position id := WriteSourceRegistry.originalSlot_index ..
  rw [index] at got
  have located := congrArg (fun xs : List (List (Array F)) => xs[WriteSourceRegistry.position id]?) arrays
  simp only [List.getElem?_map, got, Option.map_some] at located
  rw [List.getElem?_append_left (by change WriteSourceRegistry.position (.finalizer ram) < 6; cases ram <;> decide)] at located
  cases ram <;> exact Option.some.inj located

/-- Once a touched location has finished its last transfer, the genuine row of its installed
register or RAM finalizer covers every remaining representable query clock with its posted word. -/
theorem build_terminal_covers (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered)
    (history : MemoryLocationHistory) (listed : history ∈ memoryLocationHistories stream) (legal : ValidKey history.loc.busAddress)
    (time : ℕ) (exhausted : history.last.current ≤ time) (fits : time < 2 ^ 48) :
    let w := build image source target endQueue stream requested canonical data hint header suffix registered
    ∃ r ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)),
      Counted.Covers r ⟨Address.ofNat history.loc.busAddress, Address.ofNat time, Target.bitVecToWord history.last.pushed⟩ := by
  intro w
  let row := terminalOfEntry (p := SP1Prime) history.finalEntry
  have terminal : row ∈ terminals source.sail.memorySnapshot stream requested data hint :=
    List.mem_mergeSort.mpr (List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem listed)))
  have live := final_mem_live_of_rows (WriteSourceRegistry.raw w) _ data _
    (finalizer_rows image source target endQueue stream requested canonical data hint header suffix registered) row terminal
  refine ⟨finalReadback row.record, live, ?_⟩
  have covered := Counted.covers_compiled_entry (p := SP1Prime) history.finalEntry (2 ^ 48 - 1) time legal exhausted (by omega) (by decide)
  change Counted.Covers (finalReadback row.record)
    ⟨Address.ofNat history.loc.busAddress, Address.ofNat time, Target.bitVecToWord (BitVec.ofNat 64 history.last.pushed.toNat)⟩ at covered
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using covered

/-- Every valid untouched x12 or guest RAM request has a covering source on the actual
supervisor witness, after canonicalizing all 98 tables and selecting the original physical
finalizer by its registered slot. -/
theorem build_sparse_covers (image : ProgramImage) (source target : ExecutionSnapshot) (endQueue : HostHintQueue.State F)
    (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (suffix : List (Table F)) (registered)
    (key : ℕ) (wanted : key ∈ requested) (legal : ValidKey key) (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (time : ℕ) (bound : time < 2 ^ 48) :
    let w := build image source target endQueue stream requested canonical data hint header suffix registered
    ∃ loc : MemLoc, loc.busAddress = key ∧ ∃ r ∈ Counted.live (AccessInventory.records (WriteSourceRegistry.raw w)),
      Counted.Covers r ⟨Address.ofNat key, Address.ofNat time, Target.bitVecToWord (source.sail.memorySnapshot.read loc)⟩ :=
  sparse_live_covers_of_rows _ _ stream requested data hint _ (finalizer_rows image source target endQueue stream requested canonical data hint header suffix registered)
    key wanted legal fresh time bound

end SP1Clean.Export.WriteBoundaryBuild
