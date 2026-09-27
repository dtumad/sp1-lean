import ToClean.Air.EnsembleCheck
import ToClean.Air.EnsembleBuild
import SP1CleanTest.Core.EnsembleExport

/-! # Regression checks for finite ensemble acceptance

The same physical witness is checked against the raw statement theorem. Mutations separate
fixed membership, public boundary balance, and occurrence counts; disabled interactions still
consume capacity. These computations use the test library's existing compiler trust boundary.
-/

namespace SP1CleanTest.Core.EnsembleCheck

open Air.Flat Circuit
open SP1CleanTest.Core.EnsembleExport

/-- Static lookups need no prover-supplied data. -/
def data : ProverData Fp := fun _ _ => #[]

/-- Physical provider rows with the exact public input retained in the verifier. -/
def witness (publicInput : Fp) (rows : List Fp) : EnsembleWitness ensemble :=
  EnsembleWitness.ofTables ensemble
    [Table.build ⟨provider⟩ rows data (ProverHint.empty Fp)] data publicInput rfl (by
      intro table member
      obtain rfl := List.mem_singleton.mp member
      rfl)

/-- Both allowed values accept; malformed membership and boundary inventories reject. -/
def outcomes : List (String × Bool × Bool) :=
  [("allowed-seven", true, description.checkWitness SP1Clean.SP1Prime (witness 7 [7])),
   ("allowed-nine", true, description.checkWitness SP1Clean.SP1Prime (witness 9 [9])),
   ("forbidden-eight", false, description.checkWitness SP1Clean.SP1Prime (witness 8 [8])),
   ("missing-provider", false, description.checkWitness SP1Clean.SP1Prime (witness 7 [])),
   ("duplicate-provider", false, description.checkWitness SP1Clean.SP1Prime (witness 7 [7, 7])),
   ("wrong-public-input", false, description.checkWitness SP1Clean.SP1Prime (witness 9 [7]))]

/-- Every named outcome comes from checking the physical witness. -/
theorem outcomes_correct : outcomes.all (fun outcome => outcome.2.1 == outcome.2.2) = true := by
  native_decide

/-- The computed positive case proves the actual raw Clean statement. -/
theorem accepted_statement : ensemble.Statement 7 :=
  description.statement_of_checkWitness SP1Clean.SP1Prime (witness 7 [7]) (by native_decide)

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A field-small channel used only to expose the strict occurrence limit. -/
def tinyChannel : Channel (ZMod 3) field where
  name := "tiny"
  Guarantees _ _ := True

/-- Disabled interactions still occupy a position in the physical ledger. -/
def disabled : Interaction (ZMod 3) :=
  ⟨tinyChannel.toRaw, 0, #[0], rfl, false⟩

/-- Disabled occurrences below the characteristic are admissible. -/
theorem below_capacity : checkInteractionBalance 3 [disabled, disabled] = true := by native_decide

/-- Multiplicity zero does not bypass the strict characteristic limit. -/
theorem at_capacity : checkInteractionBalance 3 [disabled, disabled, disabled] = false := by native_decide

/-- The failed capacity check implies failure of the original raw predicate. -/
theorem disabled_capacity_is_raw : ¬ BalancedInteractions [disabled, disabled, disabled] := by
  rw [← checkInteractionBalance_iff 3]
  exact Bool.false_ne_true ∘ (at_capacity.symm.trans ·)

/-- A verifier assertion is checked even when the physical table inventory is empty. -/
def assertedVerifier : GeneralFormalCircuit Fp field unit where
  main value := assertZero (value - 7)
  Spec value _ _ := value = 7
  ProverAssumptions value _ _ := value = 7
  soundness := by
    circuit_proof_start
    exact sub_eq_zero.mp h_holds
  completeness := by
    circuit_proof_start
    simp_all

/-- The public verifier alone is a legitimate ensemble. -/
def boundaryEnsemble : Ensemble Fp field where
  tables := []
  channels := []
  verifier := assertedVerifier
  verifier_length_zero := by intro value; rfl

/-- The empty lookup/channel inventories are complete for this assertion-only verifier. -/
def boundaryDescription : Air.Flat.EnsembleExport boundaryEnsemble where
  componentNames := []
  names_length := rfl
  verifierName := "boundary"
  names_unique := by simp
  names_nonempty := by simp
  channels_unique := by simp [boundaryEnsemble]
  channels_nonempty := by simp [boundaryEnsemble]
  lookups := []
  lookups_unique := by simp
  lookups_nonempty := by simp
  lookups_complete := by
    simp [boundaryEnsemble, Ensemble.allTables, Ensemble.verifierTable, assertedVerifier,
      Component.rowOperations, circuit_norm]
  channels_complete := by
    simp [boundaryEnsemble, Ensemble.allTables, Ensemble.verifierTable, assertedVerifier,
      Component.rowOperations, circuit_norm]

/-- Public input is retained even with no prover tables. -/
def boundaryWitness (value : Fp) : EnsembleWitness boundaryEnsemble :=
  EnsembleWitness.ofTables boundaryEnsemble [] data value rfl (by simp)

/-- The satisfying public assertion accepts. -/
theorem verifier_accepts :
    boundaryDescription.checkWitness SP1Clean.SP1Prime (boundaryWitness 7) = true := by native_decide

/-- An invalid public assertion rejects independently of any row or balance checks. -/
theorem verifier_rejects :
    boundaryDescription.checkWitness SP1Clean.SP1Prime (boundaryWitness 9) = false := by native_decide

end SP1CleanTest.Core.EnsembleCheck
