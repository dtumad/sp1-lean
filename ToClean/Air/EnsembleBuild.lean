module

public import Clean.Air.FlatEnsemble

/-! # Constructing ensemble witnesses from committed tables

Clean's ensemble witness uses indexed layout obligations. This constructor discharges them
from one component-list equation, and derives prover data from the same physical rows through
Clean's canonical `deriveProverData`. Callers cannot supply an unrelated data environment.

The constructor belongs beside `EnsembleWitness` upstream. Delete this extension if upstream
provides the list-level introduction rule.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every arity of a named data entry is determined by its actual physical table. -/
theorem EnsembleWitness.data_of_mem_table {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) {table : Table F} (member : table ∈ witness.tables) (arity : ℕ) :
    witness.data table.component.circuit.name arity = table.component.proverRows table.table arity := by
  apply deriveProverData_eq_of_mem witness.tables _ member arity
  have unique := ens.unique_names
  rw [← witness.tables_map_component, List.map_map] at unique
  exact unique

/-- Keeping a complete physical table preserves its named data entry, even if other tables change. -/
theorem EnsembleWitness.data_eq_of_common_table {ens : Ensemble F PublicIO}
    {OtherIO : TypeMap} [ProvableType OtherIO] {other : Ensemble F OtherIO}
    (first : EnsembleWitness ens) (second : EnsembleWitness other) {table : Table F}
    (firstMember : table ∈ first.tables) (secondMember : table ∈ second.tables) (arity : ℕ) :
    first.data table.component.circuit.name arity = second.data table.component.circuit.name arity := by
  rw [first.data_of_mem_table firstMember, second.data_of_mem_table secondMember]

/-- Assemble the public input and physical tables in the ensemble's declared order. -/
def EnsembleWitness.ofTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables) :
    EnsembleWitness ens where
  tables := tables
  publicInput := publicInput
  same_length := by rw [← hmap, List.length_map]
  same_circuits := by
    intro i hi
    have hi' : i < (tables.map (·.component)).length := by rw [hmap]; exact hi
    rw [← List.getElem_of_eq hmap hi', List.getElem_map]

/-- Construction preserves every physical table and its position. -/
@[simp] theorem EnsembleWitness.ofTables_tables (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).tables = tables := rfl

/-- The environment is derived from the supplied committed rows. -/
@[simp] theorem EnsembleWitness.ofTables_data (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).data = deriveProverData tables := rfl

/-- Construction preserves the public input. -/
@[simp] theorem EnsembleWitness.ofTables_publicInput (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).publicInput = publicInput := rfl

end Air.Flat
