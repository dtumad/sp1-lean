import SP1Clean.FormalModel.Contracts.CommitmentBoundary
import Clean.Gadgets.Equality
import ToClean.Air.PublicVerifier
import ToClean.Circuit.SubcircuitProjection

/-! # Public encoding of an immutable commitment statement

The verifier binds the digest bytes, deferred field elements and rolling flags to the same
instance that fixes the declaration provider. Canonical deferred words are checked even when
there are no calls. No equation identifies an incomplete mutable bank with a full digest.
-/

namespace SP1Clean.CommitmentBoundary

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]


/-- Check canonical public fields against the fixed statement. -/
def main (statement : CommitmentStatement) (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if statement.WellFormed p then 0 else 1))
  assertion (Gadgets.Equality.circuit (fields 32)) (input.committed_value_digest, const (committed statement))
  assertion (Gadgets.Equality.circuit (fields 8)) (input.deferredProofsDigest, const (deferred statement))
  assertZero (input.commitSyscall - .const (if statement.commit then 1 else 0))
  assertZero (input.commitDeferredSyscall - .const (if statement.commitDeferred then 1 else 0))

instance elaborated (statement : CommitmentStatement) :
    ElaboratedCircuit (ZMod p) SP1PublicIO unit (main statement) := by elaborate_circuit

private theorem eval_const_vector {n : ℕ} (env : Environment (ZMod p)) (values : Vector (ZMod p) n) :
    Vector.map (Expression.eval env) (Vector.map Expression.const values) = values := by
  simp only [Vector.map_map, Function.comp_def, Expression.eval]
  exact Vector.map_id values

theorem soundness (statement : CommitmentStatement) :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) (main statement)
      (fun _ _ => True) (fun input _ _ => Spec statement input) := by
  circuit_proof_start [Gadgets.Equality.circuit]
  rw [eval_const_vector, eval_const_vector] at h_holds
  obtain ⟨valid, publicDigest, deferredDigest, flag, deferredFlag⟩ := h_holds
  refine ⟨?_, publicDigest, deferredDigest, sub_eq_zero.mp flag, sub_eq_zero.mp deferredFlag⟩
  by_contra invalid
  simp [invalid] at valid

theorem completeness (statement : CommitmentStatement) :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) (main statement)
      (fun input _ _ => Spec statement input) (fun _ _ _ => True) := by
  circuit_proof_start [Gadgets.Equality.circuit]
  rw [eval_const_vector, eval_const_vector]
  obtain ⟨valid, publicDigest, deferredDigest, flag, deferredFlag⟩ := h_assumptions
  exact ⟨by simp [valid], publicDigest, deferredDigest, sub_eq_zero.mpr flag, sub_eq_zero.mpr deferredFlag⟩

/-- Bundled public encoding assertion with semantic soundness and completeness. -/
def circuit (statement : CommitmentStatement) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := main statement
  elaborated := elaborated statement
  Spec input _ _ := Spec statement input
  ProverAssumptions input _ _ := Spec statement input
  soundness := soundness statement
  completeness := completeness statement

/-- Install the statement checks in the separate public verifier, without a trace row. -/
def checker (statement : CommitmentStatement) : PublicVerifier (ZMod p) SP1PublicIO where
  name := "commitment_statement"
  circuit := circuit statement
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; simp [circuit, main, Gadgets.Equality.circuit, Gadgets.Equality.main, circuit_norm]
  interactions := by intros; simp [circuit, main, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit_interactions, circuit_norm]

/-- Raw acceptance of the statement checks establishes the encoding, including well-formedness. -/
theorem spec_of_checks (statement : CommitmentStatement) {input : SP1PublicIO (ZMod p)} {data : ProverData (ZMod p)}
    (checked : (checker statement).Checks input data) : Spec statement input := by
  have silent : (((checker statement).circuit.main (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).FullGuarantees (Environment.fromInput input data) := by
    simp [Operations.FullGuarantees, (checker statement).interactions]
  have sound := ((checker statement).circuit.original_full_soundness (size SP1PublicIO)
    (Environment.fromInput input data) (varFromOffset SP1PublicIO 0) ((checker statement).assumptions _ _)
    checked silent).1
  rwa [ProvableType.eval_fromInput_varFromOffset_zero] at sound

theorem count_bound [Fact (2 ^ 25 < p)] (statement : CommitmentStatement) :
    (checker (p := p) statement).CountBound := by
  simp only [PublicVerifier.CountBound, PublicVerifier.assertions, checker, circuit, main,
    Gadgets.Equality.circuit, Gadgets.Equality.main, circuit_norm]
  change 2 * 43 < ringChar (ZMod p) ∨ ringChar (ZMod p) = 0
  rw [ZMod.ringChar_zmod_n]
  left
  have := Fact.out (p := 2 ^ 25 < p)
  omega

end SP1Clean.CommitmentBoundary
