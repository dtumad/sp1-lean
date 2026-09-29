module

public import ToClean.Air.EnsembleExport

/-! # Executable checking of a finite flat-ensemble witness

## Gap against upstream

Clean defines raw witness constraints and balanced channels as propositions. The finite lookup
inventory in `EnsembleExport` authenticates executable membership and channel names, but does not
yet connect a computed acceptance result to those propositions. This checker evaluates the actual
physical rows, including the public verifier, and proves exactly that connection. It checks the
characteristic bound per channel, retaining duplicate and zero-multiplicity occurrences.

The characteristic is an executable argument whose `CharP` instance authenticates the correctness
theorem. Witness generation, serialization and execution semantics are separate interfaces.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- Check the complete finite support and the raw occurrence capacity of an interaction list. -/
def checkInteractionBalance (characteristic : ℕ) (interactions : List (Interaction F)) : Bool :=
  decide (interactions.length < characteristic ∨ characteristic = 0) &&
    interactions.all (fun interaction => balanceOf interactions interaction.msg == 0)

/-- Messages outside the enumerated support have zero balance as well. -/
theorem checkInteractionBalance_iff (characteristic : ℕ) [CharP F characteristic]
    (interactions : List (Interaction F)) :
    checkInteractionBalance characteristic interactions = true ↔ BalancedInteractions interactions := by
  simp only [checkInteractionBalance, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, BalancedInteractions, ringChar.eq F characteristic]
  apply and_congr_right
  intro _
  constructor
  · intro checked message
    by_cases present : ∃ interaction ∈ interactions, interaction.msg = message
    · obtain ⟨interaction, member, rfl⟩ := present
      exact checked interaction member
    · have empty : interactions.filter (fun interaction => interaction.msg = message) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro interaction member
        exact fun equal => present ⟨interaction, member, of_decide_eq_true equal⟩
      simp only [balanceOf, empty, List.map_nil, List.sum_nil]
  · intro checked interaction _
    exact checked interaction.msg

namespace Table

/-- Evaluate every physical row's interactions selected by an exported channel name. -/
def interactionsNamed (table : Table F) (name : String) : List (Interaction F) :=
  table.table.flatMap fun row =>
    (table.component.exportInteractionsNamed name).map (·.eval (table.environment row))

end Table

namespace EnsembleWitness

/-- The named ledger includes the verifier row and every physical table occurrence. -/
def interactionsNamed (witness : EnsembleWitness ens) (name : String) : List (Interaction F) :=
  witness.allTables.flatMap (·.interactionsNamed name)

end EnsembleWitness

namespace EnsembleExport

/-- Evaluate assertions and authenticated fixed lookups in the component's real row program. -/
def checkRow (description : EnsembleExport ens) (component : Component F)
    (env : Environment F) : Bool :=
  component.rowOperations.constraints.all (fun expression => env expression == 0) &&
    component.rowOperations.lookups.all (fun lookup =>
      description.containsFixed lookup.table.name (lookup.entry.map env).toArray)

/-- Row checking is exactly the original Clean constraint predicate, including subcircuits. -/
theorem checkRow_iff (description : EnsembleExport ens) {component : Component F}
    (member : component ∈ ens.allTables) (env : Environment F) :
    description.checkRow component env = true ↔ component.operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [checkRow, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    Operations.ConstraintsHold]
  apply and_congr_right
  intro _
  exact forall₂_congr fun lookup used => description.containsFixed_iff member used env

/-- Check every physical row of a table without rebuilding or replacing its witness cells. -/
def checkTable (description : EnsembleExport ens) (table : Table F) : Bool :=
  table.table.all (fun row => description.checkRow table.component (table.environment row))

/-- Finite table checking agrees with the table's raw constraints. -/
theorem checkTable_iff (description : EnsembleExport ens) {table : Table F}
    (member : table.component ∈ ens.allTables) :
    description.checkTable table = true ↔ table.Constraints := by
  simp only [checkTable, List.all_eq_true, Table.Constraints]
  exact forall₂_congr fun row _ => description.checkRow_iff member (table.environment row)

omit [DecidableEq F] in
/-- Names select exactly the registered channel, with no loss of disabled occurrences. -/
theorem table_interactionsNamed_eq (description : EnsembleExport ens) {table : Table F}
    (member : table.component ∈ ens.allTables) {channel : RawChannel F}
    (registered : channel ∈ ens.channels) :
    table.interactionsNamed channel.name = table.interactionsWith channel := by
  simp only [Table.interactionsNamed, Table.interactionsWith,
    description.interactionsNamed_eq member registered, Operations.interactionValuesWith]

omit [DecidableEq F] in
/-- The complete executable ledger is the original ensemble's channel projection. -/
theorem witness_interactionsNamed_eq (description : EnsembleExport ens)
    (witness : EnsembleWitness ens) {channel : RawChannel F}
    (registered : channel ∈ ens.channels) :
    witness.interactionsNamed channel.name = witness.interactionsWith channel := by
  unfold EnsembleWitness.interactionsNamed EnsembleWitness.interactionsWith
  apply List.flatMap_congr
  intro table member
  exact description.table_interactionsNamed_eq
    (EnsembleWitness.mem_allTables_component_of_mem_allTables member) registered

/-- Check raw constraints and complete balances, with the exact per-channel capacity bound. -/
def checkWitness (description : EnsembleExport ens) (characteristic : ℕ)
    (witness : EnsembleWitness ens) : Bool :=
  witness.allTables.all description.checkTable &&
    ens.channels.all (fun channel =>
      checkInteractionBalance characteristic (witness.interactionsNamed channel.name))

/-- Computed acceptance is equivalent to the two raw Clean witness predicates. -/
theorem checkWitness_iff (description : EnsembleExport ens) (characteristic : ℕ)
    [CharP F characteristic] (witness : EnsembleWitness ens) :
    description.checkWitness characteristic witness = true ↔
      witness.Constraints ∧ witness.BalancedChannels := by
  simp only [checkWitness, Bool.and_eq_true, List.all_eq_true,
    EnsembleWitness.Constraints, EnsembleWitness.BalancedChannels]
  apply and_congr
  · exact forall₂_congr fun table member => description.checkTable_iff
      (EnsembleWitness.mem_allTables_component_of_mem_allTables member)
  · apply forall₂_congr
    intro channel registered
    rw [checkInteractionBalance_iff, description.witness_interactionsNamed_eq witness registered]
    rfl

/-- A checked physical witness establishes the ensemble's public statement. -/
theorem statement_of_checkWitness (description : EnsembleExport ens) (characteristic : ℕ)
    [CharP F characteristic] (witness : EnsembleWitness ens)
    (checked : description.checkWitness characteristic witness = true) :
    ens.Statement witness.publicInput :=
  ⟨witness, rfl, (description.checkWitness_iff characteristic witness).mp checked⟩

end EnsembleExport

end Air.Flat
