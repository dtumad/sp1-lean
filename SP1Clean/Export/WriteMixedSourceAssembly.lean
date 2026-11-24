import SP1Clean.Export.WriteMixedSourceTables

/-! # Installing every mixed Memory producer in the native supervisor

The memory compiler owns the two boundary finalizers and the 29 instruction, host and refresh
tables. Only the remaining physical slots take their tables from other component generators.
Canonical assembly preserves every selected cell and every unit read-back occurrence.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Semantics Soundness TraceGen Machine FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

private abbrev components := (base image source target finish).tables.drop 6

/-- The other generators provide precisely the post-boundary slots that do not publish
Memory read-backs. The index rules out supplying replacements for any Memory producer. -/
def Remaining := (i : Fin (components image source target finish).length) → sourceAt (6 + i.val) = none →
  { t : Table F // t.component = (components image source target finish)[i] }

/-- The 98-table supervisor has exactly 63 complementary slots after the six ordered boundaries
and the 29 remaining Memory publishers have been installed. -/
theorem remaining_count :
    ((List.range' 6 (components image source target finish).length).filter (fun i => (sourceAt i).isNone)).length = 63 := by
  rw [show (components image source target finish).length = 92 from
    (List.length_drop.trans (by rw [base_length]))]
  decide

variable (rows : List MixedCompiledRow) (words : List (Bool × HintReadWordChip.RowInput F))
    (fit : Heights rows words) (data : ProverData F) (hint : ProverHint F)
    (remaining : Remaining image source target finish)

private noncomputable def selectedAt (i : Fin (components image source target finish).length) :
    { t : Table F // t.component = (components image source target finish)[i] } :=
  match found : sourceAt (6 + i.val) with
  | none => remaining i found
  | some id =>
    have pos := position_of_sourceAt found
    ⟨table rows words fit data hint id (by omega), by
      rw [registered]
      have atSlot := original_at image source target finish id
      rw [pos, ← List.getElem?_drop, List.getElem?_eq_getElem i.isLt] at atSlot
      exact (Option.some.inj atSlot).symm⟩

/-- The suffix in physical registry order, using generated sources and the other installed generators. -/
noncomputable def suffix : List (Table F) :=
  List.ofFn fun i => (selectedAt image source target finish rows words fit data hint remaining i).1

/-- Any complementary generator retains the literal table it supplies at its own position. -/
theorem suffix_remaining (i : Fin (components image source target finish).length)
    (absent : sourceAt (6 + i.val) = none) :
    (suffix image source target finish rows words fit data hint remaining)[i.val]? = some (remaining i absent).1 := by
  rw [List.getElem?_eq_getElem (by simpa only [suffix, List.length_ofFn] using i.isLt)]
  simp only [suffix, List.getElem_ofFn, selectedAt]
  split
  · rfl
  · rename_i id found
    have impossible : (none : Option Source) = some id := absent.symm.trans found
    cases impossible

/-- Every slot has exactly its original registered circuit and generation procedure. -/
theorem suffix_registered : (suffix image source target finish rows words fit data hint remaining).map (·.component) =
    (base image source target finish).tables.drop 6 := by
  apply List.ext_getElem
  · simp only [suffix, List.length_map, List.length_ofFn]
  · intro i bound _
    simp only [suffix, List.getElem_map, List.getElem_ofFn]
    exact (selectedAt image source target finish rows words fit data hint remaining ⟨i, by simpa only [suffix, List.length_map, List.length_ofFn] using bound⟩).2

private theorem suffix_at (id : Source) (outside : 6 ≤ position id) :
    (suffix image source target finish rows words fit data hint remaining)[position id - 6]? =
      some (table rows words fit data hint id outside) := by
  have inBase := (List.getElem?_eq_some_iff.mp (original_at image source target finish id)).1
  have bound : position id - 6 < (components image source target finish).length := by
    simp only [components, List.length_drop]
    omega
  have found : sourceAt (6 + (position id - 6)) = some id := by
    rw [show 6 + (position id - 6) = position id by omega, sourceAt_position]
  rw [List.getElem?_eq_getElem (by simpa only [suffix, List.length_ofFn] using bound)]
  simp only [suffix, List.getElem_ofFn]
  unfold selectedAt
  split
  · rename_i h
    change sourceAt (6 + (position id - 6)) = none at h
    have impossible : (none : Option Source) = some id := h.symm.trans found
    cases impossible
  · rename_i other h
    obtain rfl := Option.some.inj (h.symm.trans found)
    rfl

/-- All 29 generated sources discharge their own constraints and guarantees. Other table
generators need certify only the slots they actually supply. -/
theorem suffix_valid {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (checked : ∀ i absent, let t := (remaining i absent).1; t.Constraints ∧ t.Guarantees) :
    ∀ t ∈ suffix image source target finish rows (HintReadTransfers.history image source events) (heights run routed)
      data hint remaining, t.Constraints ∧ t.Guarantees := by
  intro t member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  dsimp only [selectedAt]
  split
  · exact checked i _
  · exact valid run routed data hint _ _

/-- A generated supervisor with the complete set of original WRITE-read source slots. -/
noncomputable def build (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (header : SP1PublicIO F) : EnsembleWitness (base image source target finish) :=
  WriteBoundaryBuild.build image source target finish stream requested canonical data hint header
    (suffix image source target finish rows words fit data hint remaining)
    (suffix_registered image source target finish rows words fit data hint remaining)

/-- At a complementary generator's position, canonical data retains its entire physical array. -/
theorem remaining_arrays (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (header : SP1PublicIO F) (i : Fin (components image source target finish).length)
    (absent : sourceAt (6 + i.val) = none) :
    let w := build image source target finish rows words fit data hint remaining stream requested canonical header
    (w.tables.map Table.table)[6 + i.val]? = some (remaining i absent).1.table := by
  intro w
  let head := WriteBoundaryBuild.boundaryTables source.sail.memorySnapshot stream requested canonical data hint
  let tail := suffix image source target finish rows words fit data hint remaining
  have arrays : w.tables.map Table.table = (head ++ tail).map Table.table := by
    dsimp only [w, build, WriteBoundaryBuild.build]
    rw [EnsembleWitness.ofTables_tables, withDerivedData_map_table]
  rw [arrays, List.getElem?_map, List.getElem?_append_right (show head.length ≤ 6 + i.val from Nat.le_add_right _ _),
    show head.length = 6 from rfl, Nat.add_sub_cancel_left, show tail[i.val]? = _ from suffix_remaining
      image source target finish rows words fit data hint remaining i absent]
  rfl

/-- Canonical global prover-data derivation preserves the generated row arrays at every registered
ordinary, ECALL, HINT_READ and register refresh source. -/
theorem raw_rows (stream : List MemoryHistoryAccess) (requested : List ℕ) (canonical : MemoryAddressesCanonical stream)
    (header : SP1PublicIO F) (id : Source) (outside : 6 ≤ position id) :
    let w := build image source target finish rows words fit data hint remaining stream requested canonical header
    (raw w id).table = (table rows words fit data hint id outside).table := by
  let w := build image source target finish rows words fit data hint remaining stream requested canonical header
  let boundary := WriteBoundaryBuild.boundaryTables source.sail.memorySnapshot stream requested canonical data hint
  let tail := suffix image source target finish rows words fit data hint remaining
  have arrays : w.tables.map (·.table) = (boundary ++ tail).map (·.table) := by
    dsimp only [w, build, WriteBoundaryBuild.build]
    rw [EnsembleWitness.ofTables_tables, withDerivedData_map_table]
  let slot := originalSlot image source target finish id
  have got : w.tables[slot.index.val]? = some (raw w id) :=
    List.getElem?_eq_getElem (by rw [← w.same_length]; exact slot.index.isLt)
  rw [show slot.index.val = position id from originalSlot_index ..] at got
  have located := congrArg (fun xs : List (List (Array F)) => xs[position id]?) arrays
  simp only [List.getElem?_map, got, Option.map_some] at located
  rw [List.getElem?_append_right (show boundary.length ≤ position id from outside),
    show boundary.length = 6 from rfl, show tail[position id - 6]? = _ from suffix_at image source target finish rows words fit data hint remaining id outside] at located
  exact Option.some.inj located

end SP1Clean.Export.WriteMixedSourceTables
