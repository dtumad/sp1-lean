module

public import ToClean.Air.EnsembleProjection
public import ToClean.Air.LookupFree
public import ToClean.Air.TableSlot

/-! # Exact ledgers after appending physical tables

Clean provides individual table witnesses and a public verifier. For an installation that
appends tables, the original witness can be recovered from their physical prefix. Canonical
data may change under projection. Lookup-free constraints and all interaction values survive.
The suffix's full ordered interaction list remains explicit.
-/

@[expose] public section

namespace Air.Flat.Ensemble

variable {F : Type} [FiniteField F] {Public : TypeMap} [ProvableType Public]

/-- An installation leaves the physical prefix and the public verifier intact. -/
structure AppendedTables (base whole : Ensemble F Public) (extra : List (Component F)) : Prop where
  tables : whole.tables = base.tables ++ extra
  verifier : whole.verifier = base.verifier

namespace AppendedTables

variable {base whole : Ensemble F Public} {extra : List (Component F)}
  (layout : AppendedTables base whole extra)

include layout in
theorem prefix_length : base.tables.length ≤ whole.tables.length := by rw [layout.tables, List.length_append]; omega

theorem prefix_component (i : Fin base.tables.length) :
    (whole.tables[i.val]'(i.isLt.trans_le layout.prefix_length)) = base.tables[i.val] := by
  simp only [layout.tables, List.getElem_append_left i.isLt]

/-- The prefix witness uses the original table components and reconstructs its own canonical data. -/
def project (w : EnsembleWitness whole) : EnsembleWitness base :=
  w.projectPrefix base layout.prefix_length (fun i => (congrArg Component.width (layout.prefix_component i)).symm.le)
    (fun i => (congrArg Component.FixedRowsMatch (layout.prefix_component i)).symm)

theorem publicInput (w : EnsembleWitness whole) : (layout.project w).publicInput = w.publicInput := rfl

/-- Every constraint on the original physical rows survives the change of canonical data when
the retained components do not perform legacy data-dependent lookups. -/
theorem constraints (w : EnsembleWitness whole) (free : LookupFree base.tables) (checked : w.Constraints) :
    (layout.project w).Constraints := by
  apply w.projectPrefix_constraints_of _ _ _ _ checked
  intro index row width valid
  rw [layout.prefix_component index] at valid width
  rw [← width, Array.extract_size]
  exact free.constraintsHold_setData (List.getElem_mem _) valid

include layout in
/-- Reading the omitted tables recovers exactly the new installed components. -/
theorem suffix_components (w : EnsembleWitness whole) :
    (w.tables.drop base.tables.length).map (·.component) = extra := by
  rw [List.map_drop, w.tables_map_component, layout.tables, List.drop_left]

/-- The old verifier and all old physical tables form a genuine witness's ledger. Every
interaction in appended rows follows in its original order, including zeros. -/
theorem ledger (w : EnsembleWitness whole) (ch : RawChannel F) :
    w.interactionsWith ch = (layout.project w).interactionsWith ch ++
      (w.tables.drop base.tables.length).flatMap (·.interactionsWith ch) := by
  have verified : (layout.project w).verifierInteractionsWith ch = w.verifierInteractionsWith ch := by
    simp only [EnsembleWitness.verifierInteractionsWith, Ensemble.verifierOperations, layout.verifier]
    exact Operations.interactionValuesWith_congr rfl
  have prefixLedger := w.projectPrefix_tables_interactions (target := base) layout.prefix_length
    (fun i => (congrArg Component.width (layout.prefix_component i)).symm.le)
    (fun i => (congrArg Component.FixedRowsMatch (layout.prefix_component i)).symm) ch (by
      intro index row width
      rw [layout.prefix_component index] at width ⊢
      rw [← width, Array.extract_size]
      exact Component.interactionValuesWith_setData _ ch)
  change (layout.project w).tables.flatMap (·.interactionsWith ch) =
    (w.tables.take base.tables.length).flatMap (·.interactionsWith ch) at prefixLedger
  change w.verifierInteractionsWith ch ++ w.tables.flatMap (·.interactionsWith ch) =
    ((layout.project w).verifierInteractionsWith ch ++ (layout.project w).tables.flatMap (·.interactionsWith ch)) ++ _
  rw [verified, List.append_assoc, prefixLedger, ← List.flatMap_append, List.take_append_drop]

/-- An appended block silent on an original protocol leaves the complete ledger intact. -/
theorem ledger_of_silent (w : EnsembleWitness whole) (ch : RawChannel F)
    (silent : ∀ c ∈ extra, ch ∉ c.circuit.channels) :
    w.interactionsWith ch = (layout.project w).interactionsWith ch := by
  have absent : (w.tables.drop base.tables.length).flatMap (·.interactionsWith ch) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t member
    apply t.interactionsWith_nil_of_channel_not_mem
    apply silent t.component
    rw [← layout.suffix_components w]
    exact List.mem_map_of_mem member
  rw [layout.ledger, absent, List.append_nil]

/-- If only the first appended table uses a channel, its exact ledger is the appended
contribution. The selected table belongs to the whole witness and retains its data. -/
theorem ledger_first (w : EnsembleWitness whole) (ch : RawChannel F) {component : Component F}
    (slot : TableSlot whole.tables component) (position : slot.index.val = base.tables.length)
    {rest : List (Component F)} (inventory : extra = component :: rest)
    (silent : ∀ c ∈ rest, ch ∉ c.circuit.channels) :
    w.interactionsWith ch = (layout.project w).interactionsWith ch ++ (slot.table w).interactionsWith ch := by
  have inBounds : base.tables.length < w.tables.length := position ▸ w.same_length ▸ slot.index.isLt
  have first : w.tables[base.tables.length] = slot.table w := getElem_congr_idx position.symm
  have decomposition := List.drop_eq_getElem_cons inBounds
  rw [first] at decomposition
  have members := layout.suffix_components w
  rw [decomposition, List.map_cons, inventory, List.cons.injEq] at members
  have absent : (w.tables.drop (base.tables.length + 1)).flatMap (·.interactionsWith ch) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t member
    apply t.interactionsWith_nil_of_channel_not_mem
    apply silent t.component
    rw [← members.2]
    exact List.mem_map_of_mem member
  rw [layout.ledger, decomposition, List.flatMap_cons, absent, List.append_nil]

end AppendedTables
end Air.Flat.Ensemble
