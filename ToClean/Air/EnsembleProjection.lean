import ToClean.Air.EnsembleBuild

/-! # Physical witness projection between flat ensembles

Upstream Clean can split an ensemble's table list, but cannot replace components while retaining
their physical rows. An extension that adds only interactions needs this transport: project a
prefix to its original components, prove preservation of assertions and lookups, and compare each
retained channel's exact ledger. Neither row validity nor channel balance is assumed by the
constructor. The lemmas below expose the corresponding proof obligations over opaque components.
-/

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Replace only the component interpreting a table's unchanged physical rows. -/
def Table.withComponent (table : Table F) (component : Component F) : Table F :=
  { table with component := component }

theorem Table.withComponent_constraints (table : Table F) (component : Component F)
    (assertions : component.operations.constraints = table.component.operations.constraints)
    (lookups : component.operations.lookups = table.component.operations.lookups) :
    (table.withComponent component).Constraints ↔ table.Constraints := by
  simp only [Constraints, withComponent, environment, Operations.ConstraintsHold, assertions, lookups]

theorem Table.withComponent_interactions (table : Table F) (component : Component F)
    (channel : RawChannel F)
    (same : component.operations.interactionsWith channel =
      table.component.operations.interactionsWith channel) :
    (table.withComponent component).interactionsWith channel = table.interactionsWith channel := by
  simp only [interactionsWith, withComponent, environment, Operations.interactionValuesWith, same]

namespace EnsembleWitness

variable {source target : Ensemble F PublicIO}

/-- Retain a physical prefix and interpret it using the target's components. -/
def project (witness : EnsembleWitness source) (target : Ensemble F PublicIO)
    (length : target.tables.length ≤ source.tables.length) : EnsembleWitness target :=
  ofTables target (List.ofFn fun index : Fin target.tables.length =>
    (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).withComponent
      target.tables[index.val]) witness.data witness.publicInput
    (by simp only [List.map_ofFn, Table.withComponent, Function.comp_def, List.ofFn_getElem])
    (by
      intro table member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact witness.same_data
        (witness.tables[index.val]'(by rw [← witness.same_length]; omega)) (List.getElem_mem _))

theorem project_getElem (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) (index : Fin target.tables.length) :
    (witness.project target length).tables[index.val]'(by
      rw [← (witness.project target length).same_length]; exact index.isLt) =
      (witness.tables[index.val]'(by rw [← witness.same_length]; omega)).withComponent
        target.tables[index.val] := by
  simp only [project, ofTables_tables, List.getElem_ofFn]

theorem project_verifierTable (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier) :
    (witness.project target length).verifierTable = witness.verifierTable :=
  Ensemble.verifierTable_ext verifier rfl rfl

theorem project_constraints (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier)
    (assertions : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.constraints =
        (source.tables[index.val]'(by omega)).operations.constraints)
    (lookups : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.lookups =
        (source.tables[index.val]'(by omega)).operations.lookups)
    (constraints : witness.Constraints) : (witness.project target length).Constraints := by
  rw [Constraints, forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · rw [project_verifierTable witness length verifier]
    exact constraints _ witness.mem_allTables_verifierTable
  · intro table member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply (Table.withComponent_constraints _ _ ?_ ?_).mpr
    · exact constraints _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _))
    · rw [← witness.same_circuits]
      exact assertions index
    · rw [← witness.same_circuits]
      exact lookups index

theorem project_tables_interactions (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length) (channel : RawChannel F)
    (same : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.interactionsWith channel =
        (source.tables[index.val]'(by omega)).operations.interactionsWith channel) :
    (witness.project target length).tables.flatMap (·.interactionsWith channel) =
      (witness.tables.take target.tables.length).flatMap (·.interactionsWith channel) := by
  have front : (List.ofFn fun index : Fin target.tables.length =>
      witness.tables[index.val]'(by rw [← witness.same_length]; omega)) =
      witness.tables.take target.tables.length := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      rw [Nat.min_eq_left (by rw [← witness.same_length]; exact length)]
    · intro index hi hj
      simp only [List.getElem_ofFn, List.getElem_take]
  rw [← front]
  change (List.ofFn _).flatMap _ = _
  simp only [List.flatMap, List.map_ofFn, Function.comp_def]
  congr 2
  funext index
  apply Table.withComponent_interactions
  rw [← witness.same_circuits]
  exact same index

theorem project_interactions (witness : EnsembleWitness source)
    (length : target.tables.length ≤ source.tables.length)
    (verifier : target.verifier = source.verifier) (channel : RawChannel F)
    (same : ∀ index : Fin target.tables.length,
      target.tables[index.val].operations.interactionsWith channel =
        (source.tables[index.val]'(by omega)).operations.interactionsWith channel)
    (silent : (witness.tables.drop target.tables.length).flatMap (·.interactionsWith channel) = []) :
    (witness.project target length).interactionsWith channel = witness.interactionsWith channel := by
  simp only [interactionsWith, allTables, List.flatMap_cons]
  rw [project_verifierTable witness length verifier, project_tables_interactions witness length channel same]
  conv_rhs => rw [← List.take_append_drop target.tables.length witness.tables]
  rw [List.flatMap_append, silent, List.append_nil]

end EnsembleWitness
end Air.Flat
