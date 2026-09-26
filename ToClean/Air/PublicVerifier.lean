module

public import ToClean.Air.EnsembleBuild
public import ToClean.Circuit.SubcircuitProjection

/-! # Silent public checks in an ensemble verifier

Clean has no adapter for adding a zero-witness public-input check while retaining the exact
physical inventory and every channel ledger. This addition composes a real circuit invocation;
it does not strengthen `Statement` by an external predicate. The native resource boundary is
the concrete consumer. The raw constraint equivalence supports completeness as well as soundness.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A public check requiring no witness cells and emitting no interactions. -/
structure PublicVerifier (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- The actual verifier subcircuit. -/
  circuit : GeneralFormalCircuit F PublicIO unit
  /-- Public checks cannot allocate private cells. -/
  length_zero : ∀ input, circuit.localLength input = 0
  /-- Raw silence preserves every ledger, including unregistered channels. -/
  interactions : ∀ input offset env channel,
    ((circuit.main input).operations offset).interactionValuesWith channel env = []

namespace PublicVerifier
variable (check : PublicVerifier F PublicIO)

/-- Compose the original verifier with the public check. -/
def verifierMain (ens : Ensemble F PublicIO) (input : Var PublicIO F) : Circuit F Unit := do
  let _ ← ens.verifier input
  let _ ← check.circuit input

/-- The composed circuit keeps both semantic specifications and prover contracts. -/
def verifier (ens : Ensemble F PublicIO) : GeneralFormalCircuit F PublicIO unit where
  main := check.verifierMain ens
  Assumptions input data := ens.verifier.Assumptions input data ∧ check.circuit.Assumptions input data
  Spec input _ data := ens.verifier.Spec input () data ∧ check.circuit.Spec input () data
  ProverAssumptions input data hint :=
    ens.verifier.ProverAssumptions input data hint ∧ check.circuit.ProverAssumptions input data hint
  ProverSpec input _ hint := ens.verifier.ProverSpec input () hint ∧ check.circuit.ProverSpec input () hint
  channelsWithRequirements := ens.verifier.channelsWithRequirements ++ check.circuit.channelsWithRequirements
  soundness := by circuit_proof_all [verifierMain]
  completeness := by circuit_proof_all [verifierMain]

/-- Install a real public check, preserving table and channel inventories. -/
def install (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables
  channels := ens.channels
  verifier := check.verifier ens
  verifier_length_zero := by
    intro input
    simp only [verifier, circuit_norm]
    change ens.verifier.localLength input + check.circuit.localLength input = 0
    rw [ens.verifier_length_zero, check.length_zero, Nat.add_zero]

/-- Raw checks of the added circuit in the canonical public-input environment. -/
def Checks (input : PublicIO F) (data : ProverData F) : Prop :=
  ((check.circuit.main (varFromOffset PublicIO 0)).operations (size PublicIO)).ConstraintsHold
    (Environment.fromInput input data)

private theorem verifier_flat (ens : Ensemble F PublicIO) (input : Var PublicIO F) (offset : ℕ) :
    ((check.verifierMain ens input).operations offset).toFlat =
      ((ens.verifier.main input).operations offset).toFlat ++
        ((check.circuit.main input).operations offset).toFlat := by
  simp only [verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_toFlat,
    ens.verifier_length_zero, Nat.add_zero, List.append_nil]

/-- Adding a check changes exactly the verifier's raw constraints. -/
theorem verifier_constraints (ens : Ensemble F PublicIO) (input : PublicIO F) (data : ProverData F) :
    (check.install ens).VerifierConstraints input data ↔
      ens.VerifierConstraints input data ∧ check.Checks input data := by
  change ((check.verifierMain ens (varFromOffset PublicIO 0)).operations (size PublicIO)).ConstraintsHold
    (Environment.fromInput input data) ↔ _
  rw [← Circuit.constraintsHold_toFlat_iff, verifier_flat, FlatOperation.constraintsHold_append,
    Circuit.constraintsHold_toFlat_iff, Circuit.constraintsHold_toFlat_iff]
  rfl

/-- No channel gains even a zero-multiplicity occurrence. -/
theorem verifier_interactions (ens : Ensemble F PublicIO) (input : PublicIO F) (data : ProverData F)
    (channel : RawChannel F) :
    (check.install ens).verifierOperations.interactionValuesWith channel (Environment.fromInput input data) =
      ens.verifierOperations.interactionValuesWith channel (Environment.fromInput input data) := by
  change ((check.verifierMain ens (varFromOffset PublicIO 0)).operations (size PublicIO)).interactionValuesWith
    channel (Environment.fromInput input data) = _
  simp only [Operations.interactionValuesWith, Operations.interactionsWith,
    ← Operations.interactions_toFlat, verifier_flat, FlatOperation.interactions_append,
    List.filter_append, List.map_append]
  simp only [Operations.interactions_toFlat]
  change _ ++ ((check.circuit.main _).operations _).interactionValuesWith channel _ = _
  rw [check.interactions, List.append_nil]

/-- Forget only the extra verifier check, retaining the literal witness tables. -/
def project {ens : Ensemble F PublicIO} (witness : EnsembleWitness (check.install ens)) : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens witness.tables witness.data witness.publicInput
    witness.tables_map_component witness.same_data

/-- Public input is preserved without reducing the concrete ensemble definition. -/
@[simp] theorem project_publicInput {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).publicInput = witness.publicInput := rfl

/-- Shared prover data is unchanged. -/
@[simp] theorem project_data {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) : (check.project witness).data = witness.data := rfl

/-- Projection retains the literal physical table list. -/
@[simp] theorem project_tables {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) : (check.project witness).tables = witness.tables := rfl

/-- The same physical witness is a candidate for the strengthened ensemble. -/
def lift {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : EnsembleWitness (check.install ens) :=
  EnsembleWitness.ofTables (check.install ens) witness.tables witness.data witness.publicInput
    witness.tables_map_component witness.same_data

/-- Both directions preserve all ordinary row constraints. -/
theorem project_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness (check.install ens)) :
    witness.Constraints ↔ (check.project witness).Constraints ∧ check.Checks witness.publicInput witness.data := by
  simp only [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff,
    ← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints, verifier_constraints]
  tauto

private theorem verifier_table_interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : witness.verifierTable.interactionsWith channel =
      ens.verifierOperations.interactionValuesWith channel (Environment.fromInput witness.publicInput witness.data) := by
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    Operations.interactionValuesWith, EnsembleWitness.verifierTable_component,
    Ensemble.verifierTable_interactionsWith, EnsembleWitness.verifierTable_environment]

/-- The full interaction list, with order and repetitions, is unchanged. -/
theorem project_interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness (check.install ens))
    (channel : RawChannel F) :
    (check.project witness).interactionsWith channel = witness.interactionsWith channel := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    verifier_table_interactions, verifier_interactions]
  rfl

/-- The original occurrence bound and integer balance are preserved together. -/
theorem project_balanced [DecidableEq F] {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (check.install ens)) :
    (check.project witness).BalancedChannels ↔ witness.BalancedChannels := by
  unfold EnsembleWitness.BalancedChannels EnsembleWitness.BalancedChannel
  simp only [EnsembleWitness.interactionsWith_allTablesWitness, project_interactions]
  rfl

/-- A checked original witness satisfies the installed constraints. -/
theorem lift_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (constraints : witness.Constraints) (checked : check.Checks witness.publicInput witness.data) :
    (check.lift witness).Constraints := by
  rw [check.project_constraints]
  exact ⟨constraints, checked⟩

/-- Adding a silent check retains balance for a constructed witness. -/
theorem lift_balanced [DecidableEq F] {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (balanced : witness.BalancedChannels) : (check.lift witness).BalancedChannels :=
  (check.project_balanced _).mp balanced

/-- A data-independent public check strengthens the statement by exactly its proved meaning.
Both directions retain the same witness arrays and prover data. -/
theorem statement_iff [DecidableEq F] (ens : Ensemble F PublicIO) (meaning : PublicIO F → Prop)
    (checks : ∀ input data, check.Checks input data ↔ meaning input) (input : PublicIO F) :
    (check.install ens).Statement input ↔ ens.Statement input ∧ meaning input := by
  constructor
  · rintro ⟨witness, same, constraints, balanced⟩
    obtain ⟨original, checked⟩ := (check.project_constraints witness).mp constraints
    refine ⟨⟨check.project witness, same, original, (check.project_balanced witness).mpr balanced⟩, ?_⟩
    rw [← same]
    exact (checks ..).mp checked
  · rintro ⟨⟨witness, same, constraints, balanced⟩, spec⟩
    refine ⟨check.lift witness, same, check.lift_constraints witness constraints ?_,
      check.lift_balanced witness balanced⟩
    exact (checks ..).mpr (same ▸ spec)

end PublicVerifier
end Air.Flat
