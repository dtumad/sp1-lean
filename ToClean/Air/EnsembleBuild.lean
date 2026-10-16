module

public import Clean.Air.FlatEnsemble

/-! # Constructing ensemble witnesses from committed tables

Clean's ensemble witness uses indexed layout obligations. This constructor discharges them
from one component-list equation, and derives prover data from the same physical rows through
Clean's canonical `deriveProverData`. Callers cannot supply an unrelated data environment.

The constructor, named-data transport and complete-ledger filtering rules belong beside
`EnsembleWitness` upstream. Remove these additions when upstream provides the corresponding
list-level rules.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Canonical data depends on names and input rows, not the rest of each component's circuit. -/
theorem deriveProverData_congr {left right : List (Table F)}
    (same : List.Forall₂ (fun a b => a.component.circuit.name = b.component.circuit.name ∧
      ∀ arity, a.proverRows arity = b.proverRows arity) left right) :
    deriveProverData left = deriveProverData right := by
  induction same with
  | nil => rfl
  | cons head _ ih =>
    funext name arity
    simp only [deriveProverData, head.1, Table.proverRows] at *
    split
    · exact head.2 arity
    · exact congrFun (congrFun ih name) arity

/-- Dropping a suffix preserves every data key absent from that suffix. -/
theorem deriveProverData_append_of_not_mem (left right : List (Table F)) (name : String)
    (absent : ∀ table ∈ right, table.component.circuit.name ≠ name) (arity : ℕ) :
    deriveProverData (left ++ right) name arity = deriveProverData left name arity := by
  have empty : deriveProverData right name arity = #[] := by
    induction right with
    | nil => rfl
    | cons table tail ih =>
      simp only [deriveProverData, if_neg (absent table (by simp))]
      exact ih (fun next member => absent next (List.mem_cons_of_mem _ member))
  induction left with
  | nil => exact empty
  | cons table tail ih =>
    simp only [List.cons_append, deriveProverData]
    split
    · rfl
    · exact ih

/-- Every arity of a named data entry is determined by its actual physical table. -/
theorem EnsembleWitness.data_of_mem_table {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) {table : Table F} (member : table ∈ witness.tables) (arity : ℕ) :
    witness.data table.component.circuit.name arity = table.proverRows arity := by
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

/-- Change only ensemble metadata while retaining already-canonical tables and public input. -/
def EnsembleWitness.withEnsemble {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (target : Ensemble F PublicIO) (same : target.tables = ens.tables) : EnsembleWitness target where
  tables := witness.tables
  publicInput := witness.publicInput
  same_length := same.symm ▸ witness.same_length
  same_circuits := by
    intro index bound
    simpa only [same] using witness.same_circuits index (by simpa only [same] using bound)
  same_data := witness.same_data

/-- Assemble an inventory whose stored environments are already canonical. -/
def EnsembleWitness.ofCanonicalTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables)
    (canonical : ∀ table ∈ tables, table.data = deriveProverData tables) :
    EnsembleWitness ens where
  tables
  publicInput
  same_length := by rw [← hmap, List.length_map]
  same_circuits := by
    intro i hi
    have hi' : i < (tables.map (·.component)).length := by rw [hmap]; exact hi
    rw [← List.getElem_of_eq hmap hi', List.getElem_map]
  same_data := canonical

/-- Assemble the public input and physical tables in the ensemble's declared order. -/
def EnsembleWitness.ofTables (ens : Ensemble F PublicIO) (tables : List (Table F))
    (publicInput : PublicIO F) (hmap : tables.map (·.component) = ens.tables) :
    EnsembleWitness ens where
  tables := withDerivedData tables
  publicInput := publicInput
  same_length := by simp only [withDerivedData, List.length_map]; rw [← hmap, List.length_map]
  same_circuits := by
    intro i hi
    have same : (withDerivedData tables).map (·.component) = ens.tables :=
      (withDerivedData_map_component tables).trans hmap
    have hi' : i < ((withDerivedData tables).map (·.component)).length := by rw [same]; exact hi
    rw [← List.getElem_of_eq same hi', List.getElem_map]
  same_data := withDerivedData_data tables

/-- Construction installs the canonical environment without changing rows or their positions. -/
@[simp] theorem EnsembleWitness.ofTables_tables (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).tables = withDerivedData tables := rfl

/-- Canonicalizing the data keeps every physical row in its original position. -/
@[simp] theorem EnsembleWitness.ofTables_rows (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).tables.map (·.table) =
      tables.map (·.table) := by
  simp [ofTables, withDerivedData]

/-- The environment is derived from the supplied committed rows. -/
@[simp] theorem EnsembleWitness.ofTables_data (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).data = deriveProverData tables :=
  deriveProverData_map_data tables _

/-- Construction preserves the public input. -/
@[simp] theorem EnsembleWitness.ofTables_publicInput (ens : Ensemble F PublicIO)
    (tables : List (Table F)) (publicInput : PublicIO F)
    (hmap : tables.map (·.component) = ens.tables) :
    (EnsembleWitness.ofTables ens tables publicInput hmap).publicInput = publicInput := rfl

open Classical in
/-- Channel selection filters the complete ledger, including the public verifier's occurrences. -/
theorem EnsembleWitness.interactionsWith_eq_filter {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.interactionsWith channel = witness.interactions.filter (·.channel = channel) := by
  simp only [interactionsWith, verifierInteractionsWith, toTables,
    Tables.interactionsWith, Operations.interactionValuesWith_eq_filter,
    Table.interactionsWith_eq_filter, interactions, List.filter_append, List.filter_flatMap]

end Air.Flat
