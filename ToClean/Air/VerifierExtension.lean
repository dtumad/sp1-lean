module

public import ToClean.Air.EnsembleBuild
public import ToClean.Circuit.SubcircuitProjection

/-! # Exactly-once closed circuits in an ensemble verifier

Clean runs the verifier exactly once, but has no adapter that moves one of its closed subcircuits
into a derived singleton table while preserving the complete AIR ledger. This addition lets
ordinary table-level proofs consume verifier-owned boundary interactions without accepting a
witness-selected number of boundary rows. It belongs beside `Clean/Air/FlatEnsemble.lean`.

Zero witness length alone does not establish independence from offsets or ambient row values.
`ClosedVerifier` therefore requires exact static constraint and interaction transport laws.
The derived singleton is a representation of the real verifier invocation, not an extra source.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F]

/-- A zero-input circuit whose raw checks and interactions depend only on the shared prover data. -/
structure ClosedVerifier (F : Type) [FiniteField F] where
  circuit : GeneralFormalCircuit F unit unit
  length_zero : circuit.localLength () = 0
  constraints : ∀ offset env, ((circuit.main ()).operations offset).ConstraintsHold env ↔
    ((circuit.main ()).operations 0).ConstraintsHold (Environment.fromInput (Input := unit) () env.data)
  interactions : ∀ offset env channel,
    ((circuit.main ()).operations offset).interactionValuesWith channel env =
      ((circuit.main ()).operations 0).interactionValuesWith channel
        (Environment.fromInput (Input := unit) () env.data)

namespace ClosedVerifier

variable (closed : ClosedVerifier F)

def singleton (data : ProverData F) : Table F where
  component := ⟨closed.circuit⟩
  width := 0
  table := [#[]]
  data := data
  uniform_width := by simp

theorem singleton_constraints (data : ProverData F) :
    (closed.singleton data).Constraints ↔
      ((closed.circuit.main ()).operations 0).ConstraintsHold (Environment.fromInput (Input := unit) () data) := by
  simp only [Table.Constraints, singleton, List.mem_singleton, forall_eq]
  exact Component.constraintsHold_iff _

theorem singleton_interactions (data : ProverData F) (channel : RawChannel F) :
    (closed.singleton data).interactionsWith channel =
      ((closed.circuit.main ()).operations 0).interactionValuesWith channel (Environment.fromInput (Input := unit) () data) := by
  simp only [Table.interactionsWith, singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Operations.interactionValuesWith, Component.interactionsWith_eq]
  rfl

variable {PublicIO : TypeMap} [ProvableType PublicIO]

def verifierMain (ens : Ensemble F PublicIO) (input : Var PublicIO F) : Circuit F Unit := do
  let _ ← ens.verifier input
  let _ ← closed.circuit ()

def verifier (ens : Ensemble F PublicIO) : GeneralFormalCircuit F PublicIO unit where
  main := closed.verifierMain ens
  Assumptions input data := ens.verifier.Assumptions input data ∧ closed.circuit.Assumptions () data
  Spec input _ data := ens.verifier.Spec input () data ∧ closed.circuit.Spec () () data
  ProverAssumptions input data hint :=
    ens.verifier.ProverAssumptions input data hint ∧ closed.circuit.ProverAssumptions () data hint
  ProverSpec input _ hint := ens.verifier.ProverSpec input () hint ∧ closed.circuit.ProverSpec () () hint
  channelsWithRequirements := ens.verifier.channelsWithRequirements ++ closed.circuit.channelsWithRequirements
  soundness := by circuit_proof_all [verifierMain]
  completeness := by circuit_proof_all [verifierMain]

theorem verifier_length_zero (ens : Ensemble F PublicIO) (input : Var PublicIO F) :
    (closed.verifier ens).localLength input = 0 := by
  simp only [verifier, circuit_norm]
  change ens.verifier.localLength input + closed.circuit.localLength () = 0
  rw [ens.verifier_length_zero, closed.length_zero, Nat.add_zero]

/-- Run the closed boundary once in the verifier, retaining every ordinary physical table. -/
def install (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables
  channels := ens.channels ++ closed.circuit.channels
  verifier := closed.verifier ens
  verifier_length_zero := closed.verifier_length_zero ens

/-- The table-oriented representation used only by the derived witness below. -/
def asTable (ens : Ensemble F PublicIO) : Ensemble F PublicIO where
  tables := ens.tables ++ [⟨closed.circuit⟩]
  channels := ens.channels ++ closed.circuit.channels
  verifier := ens.verifier
  verifier_length_zero := ens.verifier_length_zero

private theorem verifier_flat (ens : Ensemble F PublicIO) (input : Var PublicIO F) (offset : ℕ) :
    ((closed.verifierMain ens input).operations offset).toFlat =
      ((ens.verifier.main input).operations offset).toFlat ++
        ((closed.circuit.main ()).operations offset).toFlat := by
  simp only [verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_toFlat,
    ens.verifier_length_zero, Nat.add_zero, List.append_nil]

theorem verifier_constraints (ens : Ensemble F PublicIO) (input : PublicIO F) (data : ProverData F) :
    (closed.install ens).VerifierConstraints input data ↔
      ens.VerifierConstraints input data ∧ (closed.singleton data).Constraints := by
  change ((closed.verifierMain ens (varFromOffset PublicIO 0)).operations (size PublicIO)).ConstraintsHold
    (Environment.fromInput input data) ↔ _
  rw [← Circuit.constraintsHold_toFlat_iff, verifier_flat, FlatOperation.constraintsHold_append,
    Circuit.constraintsHold_toFlat_iff, Circuit.constraintsHold_toFlat_iff,
    closed.constraints, ← singleton_constraints]
  rfl

theorem verifier_interactions (ens : Ensemble F PublicIO) (input : PublicIO F) (data : ProverData F)
    (channel : RawChannel F) :
    (closed.install ens).verifierOperations.interactionValuesWith channel (Environment.fromInput input data) =
      ens.verifierOperations.interactionValuesWith channel (Environment.fromInput input data) ++
        (closed.singleton data).interactionsWith channel := by
  change ((closed.verifierMain ens (varFromOffset PublicIO 0)).operations (size PublicIO)).interactionValuesWith
    channel (Environment.fromInput input data) = _
  simp only [Operations.interactionValuesWith, Operations.interactionsWith,
    ← Operations.interactions_toFlat, verifier_flat, FlatOperation.interactions_append,
    List.filter_append, List.map_append]
  simp only [Operations.interactions_toFlat]
  change _ ++ ((closed.circuit.main ()).operations (size PublicIO)).interactionValuesWith
    channel (Environment.fromInput input data) = _
  rw [closed.interactions, singleton_interactions]

/-- The single boundary row is derived from the verifier and cannot be omitted or duplicated. -/
def expand {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    EnsembleWitness (closed.asTable ens) :=
  EnsembleWitness.ofTables (closed.asTable ens) (witness.tables ++ [closed.singleton witness.data])
    witness.data witness.publicInput
    (by simp only [List.map_append, witness.tables_map_component, install,
      List.map_cons, List.map_nil, singleton, asTable])
    (by
      intro table member
      rcases List.mem_append.mp member with old | added
      · exact witness.same_data table old
      · obtain rfl := List.mem_singleton.mp added
        rfl)

@[simp] theorem expand_data {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    (closed.expand witness).data = witness.data := rfl

@[simp] theorem expand_publicInput {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    (closed.expand witness).publicInput = witness.publicInput := rfl

theorem expand_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens))
    (constraints : witness.Constraints) : (closed.expand witness).Constraints := by
  have checks := (closed.verifier_constraints ens witness.publicInput witness.data).mp
    (EnsembleWitness.verifierConstraints_of_constraints constraints)
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  refine ⟨?_, ?_⟩
  · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
    exact checks.1
  · intro table member
    rcases List.mem_append.mp member with old | added
    · exact constraints table (witness.mem_allTables_of_mem_tables old)
    · obtain rfl := List.mem_singleton.mp added
      exact checks.2

/-- The singleton representation preserves satisfiability in both directions. -/
theorem expand_constraints_iff {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens)) :
    (closed.expand witness).Constraints ↔ witness.Constraints := by
  refine ⟨?_, closed.expand_constraints witness⟩
  intro constraints
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff] at constraints ⊢
  constructor
  · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints, verifier_constraints]
    exact ⟨EnsembleWitness.verifierConstraints_iff_verifierTable_constraints.mpr constraints.1,
      constraints.2 _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · intro table member
    exact constraints.2 table (List.mem_append_left _ member)

private theorem verifier_table_interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : witness.verifierTable.interactionsWith channel =
      ens.verifierOperations.interactionValuesWith channel (Environment.fromInput witness.publicInput witness.data) := by
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    Operations.interactionValuesWith, EnsembleWitness.verifierTable_component,
    Ensemble.verifierTable_interactionsWith, EnsembleWitness.verifierTable_environment]

/-- All channels and all multiplicities are preserved, including the original count bound. -/
theorem expand_interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens))
    (channel : RawChannel F) :
    ((closed.expand witness).interactionsWith channel).Perm (witness.interactionsWith channel) := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    verifier_table_interactions]
  change (ens.verifierOperations.interactionValuesWith channel (Environment.fromInput witness.publicInput witness.data) ++
    (witness.tables ++ [closed.singleton witness.data]).flatMap (·.interactionsWith channel)).Perm _
  rw [verifier_interactions]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  exact (List.perm_append_comm ..).append_left _

theorem expand_balanced [DecidableEq F] {ens : Ensemble F PublicIO} (witness : EnsembleWitness (closed.install ens))
    (balanced : witness.BalancedChannels) : (closed.expand witness).BalancedChannels := by
  intro channel member
  exact balancedInteractions_of_perm (balanced channel member) (closed.expand_interactions witness channel).symm

theorem expand_balanced_iff [DecidableEq F] {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness (closed.install ens)) :
    (closed.expand witness).BalancedChannels ↔ witness.BalancedChannels := by
  refine ⟨?_, closed.expand_balanced witness⟩
  intro balanced channel member
  exact balancedInteractions_of_perm (balanced channel member) (closed.expand_interactions witness channel)

end ClosedVerifier
end Air.Flat
