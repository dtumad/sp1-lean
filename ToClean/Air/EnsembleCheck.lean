module

public import ToClean.Air.EnsembleBuild
public import ToClean.Air.FiniteLookup

/-! # Executable checking of finite ensemble witnesses

Clean's witness-generation checks reject legacy lookups and normalize away zero-multiplicity
occurrences. This addition authenticates finite lookup membership and proves an executable check
equivalent to the raw constraints and channel balances, including their occurrence bounds.

The checker evaluates Clean's canonical physical data and complete interaction ledger directly.
The public verifier contributes interactions, never a synthetic physical table. This API belongs
upstream beside ensemble checking; it has no serialization or witness-generation dependency.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}

/-- Finite lookup meanings and channel identities needed to execute the raw ensemble relation.
Component names and physical order are already authenticated by the ensemble itself. -/
structure EnsembleCheck (ens : Ensemble F PublicIO) where
  /-- Finite enumerations authenticated against the original lookup predicates. -/
  lookups : List (FiniteLookup F)
  lookups_unique : (lookups.map (fun lookup => lookup.table.name)).Nodup
  lookups_complete : ∀ component ∈ ens.tables, ∀ lookup ∈ component.operations.lookups,
    ∃ fixed ∈ lookups, fixed.table = lookup.table


/-- Check signed field balance on every message in the finite physical ledger. -/
def checkLogUpBalance (interactions : List (Interaction F)) : Bool :=
  interactions.all (fun interaction => balanceOf interactions interaction.msg == 0)

/-- Messages outside the enumerated support have zero balance as well. -/
theorem checkLogUpBalance_iff (interactions : List (Interaction F)) :
    checkLogUpBalance interactions = true ↔ LogUpBalanced interactions := by
  simp only [checkLogUpBalance, List.all_eq_true, beq_iff_eq, LogUpBalanced]
  constructor
  · intro checked message
    by_cases present : ∃ interaction ∈ interactions, interaction.msg = message
    · obtain ⟨interaction, member, rfl⟩ := present
      exact checked interaction member
    · have empty : interactions.filter (fun i => decide (i.msg = message)) = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq]
        intro i hi same
        exact present ⟨i, hi, same⟩
      simp [balanceOf, empty]
  · intro checked interaction _
    exact checked interaction.msg

/-- Check field balance and its complete physical occurrence bound, including disabled rows. -/
def checkInteractionBalance (characteristic : ℕ) (interactions : List (Interaction F)) : Bool :=
  decide (interactions.length < characteristic) && checkLogUpBalance interactions

theorem checkInteractionBalance_iff (characteristic : ℕ) (interactions : List (Interaction F)) :
    checkInteractionBalance characteristic interactions = true ↔
      interactions.length < characteristic ∧ LogUpBalanced interactions := by
  simp only [checkInteractionBalance, Bool.and_eq_true, decide_eq_true_eq, checkLogUpBalance_iff]

namespace EnsembleCheck

/-- Membership in the authenticated finite lookup inventory. -/
def containsFixed (description : EnsembleCheck ens) (name : String) (entry : Array F) : Bool :=
  description.lookups.any (fun fixed => fixed.table.name == name &&
    fixed.rows.any (fun row => row.toArray == entry))

/-- Lookup names identify the original predicate, independently of the prover-data environment. -/
theorem containsFixed_iff (description : EnsembleCheck ens) {component : Component F}
    (member : component ∈ ens.tables) {lookup : Lookup F}
    (used : lookup ∈ component.operations.lookups) (env : Environment F) :
    description.containsFixed lookup.table.name (lookup.entry.map env).toArray = true ↔
      lookup.Contains env := by
  obtain ⟨fixed, fixedMem, tableEq⟩ := description.lookups_complete component member lookup used
  rcases lookup with ⟨table, entry⟩
  cases tableEq
  change description.containsFixed fixed.table.name (entry.map env).toArray = true ↔
    fixed.table.Contains (env.data.tables fixed.table.name fixed.table.arity) (entry.map env)
  rw [fixed.realizes]
  simp only [containsFixed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨selected, selectedMem, nameEq, row, rowMem, rowEq⟩
    have selectedEq := List.inj_on_of_nodup_map description.lookups_unique selectedMem fixedMem nameEq
    subst selected
    rw [Vector.toArray_inj.mp rowEq] at rowMem
    exact rowMem
  · intro member
    exact ⟨fixed, fixedMem, rfl, entry.map env, member, rfl⟩

/-- Evaluate the component's actual assertions and authenticated fixed lookups. -/
def checkRow (description : EnsembleCheck ens) (component : Component F)
    (env : Environment F) : Bool :=
  component.operations.constraints.all (fun expression => env expression == 0) &&
    component.operations.lookups.all (fun lookup =>
      description.containsFixed lookup.table.name (lookup.entry.map env).toArray)

/-- Row checking agrees with Clean's constraint predicate, including nested subcircuits. -/
theorem checkRow_iff (description : EnsembleCheck ens) {component : Component F}
    (member : component ∈ ens.tables) (env : Environment F) :
    description.checkRow component env = true ↔ component.operations.ConstraintsHold env := by
  simp only [checkRow, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    Operations.ConstraintsHold]
  apply and_congr_right
  intro _
  exact forall₂_congr fun lookup used => description.containsFixed_iff member used env

/-- Check every physical row under the canonical data of its containing witness. -/
def checkTable (description : EnsembleCheck ens) (table : Table F) : Bool :=
  table.table.all (fun row =>
    description.checkRow table.component (table.environment row))

/-- Finite table checking agrees with the table's raw constraints. -/
theorem checkTable_iff (description : EnsembleCheck ens) {table : Table F}
    (member : table.component ∈ ens.tables) :
    description.checkTable table = true ↔ table.Constraints := by
  simp only [checkTable, List.all_eq_true, Table.Constraints]
  exact forall₂_congr fun row _ => description.checkRow_iff member (table.environment row)

/-- Upstream unique channel registration identifies the complete ledger by name. -/
theorem interactionsNamed_eq (_description : EnsembleCheck ens) (witness : EnsembleWitness ens)
    {channel : RawChannel F} (registered : channel ∈ ens.channels) :
    witness.interactions.filter (fun interaction => interaction.channel.name == channel.name) =
      witness.interactionsWith channel :=
  (witness.interactionsWith_eq_filter_name registered).symm

variable [ComputableRingChar F]

/-- Check raw constraints and balances without removing repeated or disabled interactions. -/
def checkWitness (description : EnsembleCheck ens)
    (witness : EnsembleWitness ens) : Bool :=
  let ledger := witness.interactions
  ens.interactionsFit .logUp witness.heights &&
    (witness.tables.all description.checkTable &&
    ens.channels.all (fun channel =>
      checkLogUpBalance
        (ledger.filter fun interaction => interaction.channel.name == channel.name)))

/-- Computed acceptance checks the height capacity as well as constraints and LogUp balance. -/
theorem checkWitness_iff (description : EnsembleCheck ens) (witness : EnsembleWitness ens) :
    description.checkWitness witness = true ↔
      ens.interactionsFit .logUp witness.heights ∧ witness.Constraints ∧ witness.Balanced .logUp := by
  simp only [checkWitness, Bool.and_eq_true, List.all_eq_true, EnsembleWitness.Constraints,
    EnsembleWitness.Balanced, Balance.logUp]
  apply and_congr_right
  intro _
  apply and_congr
  · exact forall₂_congr fun table member => description.checkTable_iff
      (EnsembleWitness.component_mem_tables_of_mem member)
  · apply forall₂_congr
    intro channel registered
    rw [checkLogUpBalance_iff, description.interactionsNamed_eq witness registered]

/-- A checked physical witness establishes the actual height-indexed LogUp statement. -/
theorem statement_of_checkWitness (description : EnsembleCheck ens) (witness : EnsembleWitness ens)
    (checked : description.checkWitness witness = true) :
    ens.Statement .logUp witness.publicInput witness.heights := by
  obtain ⟨fit, constraints, balanced⟩ := (description.checkWitness_iff witness).mp checked
  exact ⟨fit, witness, rfl, rfl, constraints, balanced⟩

end EnsembleCheck

end Air.Flat
