module

public import ToClean.Air.EnsembleProjection
public import ToClean.Air.LookupFree
public import ToClean.Air.TableSlot

/-! # Transporting physical witnesses between row-preserving ensembles

Clean's prefix projection handles unequal tables and row widths. An in-place circuit decoration
preserves a complete name and row layout in both directions. These lemmas transport witnesses,
constraints and the exact ledger of each selected channel through the same layout equivalence.
Delete this addition when Clean supplies this interface.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] {Public : TypeMap} [ProvableType Public]

/-- The physical layout and row checks agree, as do all selected original protocol occurrences. -/
structure Component.SameRows (keep : RawChannel F → Prop) (a b : Component F) : Prop where
  name : a.circuit.name = b.circuit.name
  width : a.width = b.width
  fixed : a.FixedRowsMatch = b.FixedRowsMatch
  constraints : a.operations.constraints = b.operations.constraints
  lookups : a.operations.lookups = b.operations.lookups
  interactions : ∀ channel, keep channel → a.operations.interactionsWith channel = b.operations.interactionsWith channel

theorem Component.SameRows.symm {keep : RawChannel F → Prop} {a b : Component F}
    (same : Component.SameRows keep a b) : Component.SameRows keep b a :=
  ⟨same.name.symm, same.width.symm, same.fixed.symm, same.constraints.symm, same.lookups.symm,
   fun ch h => (same.interactions ch h).symm⟩

/-- The same physical slots and public verifier, with channel preservation checked per slot. -/
structure Ensemble.SameRows (keep : RawChannel F → Prop) (a b : Ensemble F Public) : Prop where
  length : a.tables.length = b.tables.length
  verifier : a.verifier = b.verifier
  slot : ∀ i : Fin a.tables.length, Component.SameRows keep a.tables[i.val]
    (b.tables[i.val]'(length ▸ i.isLt))

namespace Ensemble.SameRows

/-- Build an in-place relabeling directly from the new registry's pointwise construction. -/
theorem ofDecoration (keep : RawChannel F → Prop) (a b : Ensemble F Public)
    (length : b.tables.length = a.tables.length) (verifier : b.verifier = a.verifier)
    (entries : ∀ i : Fin a.tables.length, Component.SameRows keep a.tables[i.val]
      (b.tables[i.val]'(by rw [length]; exact i.isLt))) : Ensemble.SameRows keep a b :=
  ⟨length.symm, verifier.symm, entries⟩
variable {keep : RawChannel F → Prop} {a b : Ensemble F Public} (same : Ensemble.SameRows keep a b)

include same in
theorem symm : Ensemble.SameRows keep b a :=
  ⟨same.length.symm, same.verifier.symm, fun i => (same.slot ⟨i.val, same.length.symm ▸ i.isLt⟩).symm⟩

include same in
/-- Row-local lookup inventories agree in every physical slot. -/
theorem lookupFree (free : LookupFree a.tables) : LookupFree b.tables := by
  intro c member
  obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
  have prior : i < a.tables.length := same.length.symm ▸ inside
  exact (same.slot ⟨i, prior⟩).lookups.symm.trans (free _ (List.getElem_mem prior))

/-- Relabel the same committed arrays, recomputing their data through the canonical typed API. -/
def transport (w : EnsembleWitness b) : EnsembleWitness a :=
  w.projectPrefix a same.length.le (fun i => (same.slot i).width.le) (fun i => (same.slot i).fixed)

theorem publicInput (w : EnsembleWitness b) : (same.transport w).publicInput = w.publicInput := rfl

theorem data (w : EnsembleWitness b) : (same.transport w).data = w.data :=
  w.projectPrefix_data_eq_of_layout _ _ _ (fun i => (same.slot i).width) (fun i => (same.slot i).name) same.length

theorem rows (w : EnsembleWitness b) (i : Fin a.tables.length) :
    ((same.transport w).tables[i.val]'(by rw [← EnsembleWitness.same_length]; exact i.isLt)).table =
      (w.tables[i.val]'(by rw [← EnsembleWitness.same_length, ← same.length]; exact i.isLt)).table :=
  w.projectPrefix_getElem_rows_of_width_eq _ _ _ i (same.slot i).width

/-- A component rebuilt from a transported slot agrees with the physical source table
when it restores the component registered there and retains the physical rows and data. -/
theorem reattach {old new : Component F} (left : TableSlot a.tables old) (right : TableSlot b.tables new)
    (position : left.index.val = right.index.val) (w : EnsembleWitness b) (rebuilt : Table F)
    (field : rebuilt.component = new ∧ rebuilt.table = (left.table (same.transport w)).table ∧
      rebuilt.data = (left.table (same.transport w)).data) : rebuilt = right.table w := by
  apply Table.ext_iff.mpr
  refine ⟨field.1.trans (right.table_component w).symm, field.2.1.trans ?_, field.2.2.trans ?_⟩
  · have h := same.rows w left.index
    change _ = (w.tables[right.index.val]'_).table
    exact h.trans (congrArg Table.table (getElem_congr_idx position))
  · exact ((same.transport w).same_data _ (left.table_mem _)).trans ((same.data w).trans (w.same_data _ (right.table_mem _)).symm)

/-- The reverse direction identifies a transported slot with a rebuilt component over the original data. -/
theorem attach {old new : Component F} (left : TableSlot a.tables old) (right : TableSlot b.tables new)
    (position : left.index.val = right.index.val) (w : EnsembleWitness b) (rebuilt : Table F)
    (field : rebuilt.component = old ∧ rebuilt.table = (right.table w).table ∧ rebuilt.data = (right.table w).data) :
    left.table (same.transport w) = rebuilt := by
  apply Table.ext_iff.mpr
  refine ⟨(left.table_component _).trans field.1.symm, ?_, ?_⟩
  · refine Eq.trans ?_ field.2.1.symm
    have h := same.rows w left.index
    change _ = (w.tables[right.index.val]'_).table
    exact h.trans (congrArg Table.table (getElem_congr_idx position))
  · exact ((same.transport w).same_data _ (left.table_mem _)).trans
      ((same.data w).trans ((w.same_data _ (right.table_mem _)).symm.trans field.2.2.symm))

/-- Transport preserves the full vector of physical heights, including empty and padded tables. -/
theorem heights (w : EnsembleWitness b) : (same.transport w).heights = w.heights := by
  apply List.ext_getElem
  · simp only [EnsembleWitness.heights, List.length_map, ← EnsembleWitness.same_length, same.length]
  · intro i left right
    have bound : i < a.tables.length := by
      simpa only [EnsembleWitness.heights, List.length_map, ← EnsembleWitness.same_length] using left
    simpa only [EnsembleWitness.heights, List.getElem_map] using congrArg List.length (same.rows w ⟨i, bound⟩)

theorem constraints (w : EnsembleWitness b) (checked : w.Constraints) : (same.transport w).Constraints := by
  apply w.projectPrefix_constraints_of _ _ _ _ checked
  intro i row size holds
  have entry := same.slot i
  have clip : row.extract 0 a.tables[i.val].width = row := by rw [entry.width, ← size, Array.extract_size]
  change a.tables[i.val].operations.ConstraintsHold (Environment.fromArray (row.extract 0 _) (same.transport w).data)
  simpa only [clip, same.data, Operations.ConstraintsHold, entry.constraints, entry.lookups] using holds

/-- Equality preserves signed values, order, repeated keys and zero-weight occurrences. -/
theorem ledger (w : EnsembleWitness b) (ch : RawChannel F) (retained : keep ch) :
    (same.transport w).interactionsWith ch = w.interactionsWith ch := by
  apply w.projectPrefix_interactions _ _ _ same.verifier ch
  · intro i row size
    have entry := same.slot i
    have clip : row.extract 0 a.tables[i.val].width = row := by rw [entry.width, ← size, Array.extract_size]
    change a.tables[i.val].operations.interactionValuesWith ch (Environment.fromArray (row.extract 0 _) (same.transport w).data) = _
    simp only [clip, same.data, Operations.interactionValuesWith, entry.interactions ch retained]
  · rw [same.length, w.same_length, List.drop_length]
    simp

end Ensemble.SameRows
end Air.Flat
