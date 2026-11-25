module

public import ToClean.Air.AppendedTables
public import ToClean.Air.EnsembleBuild

/-! # Building an extended ensemble from original and appended physical tables

Clean's canonical table constructor rebinds all rows to committed prover data. For an
append-only installation its exact height vector and complete signed ledgers split at the
original registry boundary, and lookup-free checked constraints survive the rebind.
-/

@[expose] public section

namespace Air.Flat.Ensemble.AppendedTables

open Circuit

variable {F : Type} [FiniteField F] {Public : TypeMap} [ProvableType Public]
  {base whole : Ensemble F Public} {extra : List (Component F)}
  (layout : Ensemble.AppendedTables base whole extra) (w : EnsembleWitness base)
  (suffix : List (Table F)) (registered : suffix.map (·.component) = extra)

/-- Use the physical arrays in registry order and derive the single shared data store. -/
def extend : EnsembleWitness whole :=
  EnsembleWitness.ofTables whole (w.tables ++ suffix) w.publicInput
    (by rw [List.map_append, w.tables_map_component, registered, layout.tables])

theorem extend_publicInput : (layout.extend w suffix registered).publicInput = w.publicInput :=
  EnsembleWitness.ofTables_publicInput ..

theorem extend_data : (layout.extend w suffix registered).data =
    deriveProverData (w.tables ++ suffix) (toElements w.publicInput).toArray := EnsembleWitness.ofTables_data ..

theorem extend_heights : (layout.extend w suffix registered).heights = w.heights ++ suffix.map (·.length) := by
  simp only [extend, EnsembleWitness.heights, EnsembleWitness.ofTables_tables]
  change List.map (fun t : Table F => t.table.length) (withDerivedData _ _ _) = _
  rw [show (fun t : Table F => t.table.length) = List.length ∘ Table.table by rfl, ← List.map_map,
    withDerivedData_map_table, List.map_append, List.map_append, List.map_map, List.map_map]

/-- Public verifier interactions evaluate at the same input. Row interactions from each
appended table follow all original ones, including disabled and repeated occurrences. -/
theorem extend_ledger (ch : RawChannel F) : (layout.extend w suffix registered).interactionsWith ch =
    w.interactionsWith ch ++ suffix.flatMap (·.interactionsWith ch) := by
  have verifier : (layout.extend w suffix registered).verifierInteractionsWith ch = w.verifierInteractionsWith ch := by
    simp only [EnsembleWitness.verifierInteractionsWith, Ensemble.verifierOperations, layout.verifier]
    apply Operations.interactionValuesWith_congr
    rfl
  change (layout.extend w suffix registered).verifierInteractionsWith ch ++
    (layout.extend w suffix registered).tables.flatMap (·.interactionsWith ch) = (_ ++ w.tables.flatMap _) ++ _
  rw [verifier, List.append_assoc]
  simp only [extend, EnsembleWitness.ofTables_tables, withDerivedData_interactionsWith, List.flatMap_append]

/-- All physical constraints are preserved by the one shared final-data installation. -/
theorem extend_constraints (free : LookupFree whole.tables) (prior : w.Constraints)
    (added : ∀ t ∈ suffix, t.Constraints) : (layout.extend w suffix registered).Constraints := by
  intro t member row included
  have lookups := free t.component (EnsembleWitness.component_mem_tables_of_mem member)
  rw [extend, EnsembleWitness.ofTables_tables] at member
  have mapped := List.mem_map_of_mem (f := fun t : Table F => (t.component, t.table)) member
  rw [withDerivedData_map] at mapped
  obtain ⟨old, orig, same⟩ := List.mem_map.mp mapped
  obtain ⟨component, rows⟩ := Prod.mk.inj same
  have checked := (List.mem_append.mp orig).elim (prior old) (added old)
  have holds := checked row (rows ▸ included)
  rw [component] at holds
  exact t.component.constraintsHold_setData lookups holds

end Air.Flat.Ensemble.AppendedTables
