import SP1Clean.FormalModel.Contracts.ResourceBoundary
import ToClean.Air.PublicVerifier

/-! # Native resource-boundary verifier circuit

The fixed snapshots and numeric limits are public instance data, so their finite checks are
constant assertions. Two additional equations bind the target clock to the real State ledger.
This circuit adds no cells, rows or interactions and does not change any Rust chip anchor.
-/

namespace SP1Clean.ResourceBoundary
open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- Reject an invalid endpoint budget and bind the outgoing public clock. -/
def main (limits : ResourceLimits) (source target : ExecutionSnapshot)
    (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if checkBounds limits source target then 0 else 1))
  assertZero (input.final_clk_high - .const (target.clock / 2 ^ 24 : ℕ))
  assertZero (input.final_clk_low - .const (target.clock % 2 ^ 24 : ℕ))

/-- The checked boundary is an ordinary, proof-complete Clean subcircuit. -/
def circuit (limits : ResourceLimits) (source target : ExecutionSnapshot) :
    GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := main limits source target
  Spec input _ _ := Spec limits source target input
  ProverAssumptions input _ _ := Spec limits source target input
  soundness := by
    circuit_proof_start [main]
    obtain ⟨checked, high, low⟩ := h_holds
    refine ⟨?_, sub_eq_zero.mp high, sub_eq_zero.mp low⟩
    by_cases valid : checkBounds limits source target = true
    · exact (checkBounds_iff limits source target).mp valid
    · simp [valid] at checked
  completeness := by
    circuit_proof_start [main]
    obtain ⟨bounds, high, low⟩ := h_assumptions
    exact ⟨by simp [(checkBounds_iff limits source target).mpr bounds],
      sub_eq_zero.mpr high, sub_eq_zero.mpr low⟩

/-- Installable public check with literal raw silence. -/
def checker (limits : ResourceLimits) (source target : ExecutionSnapshot) :
    PublicVerifier (ZMod p) SP1PublicIO where
  circuit := circuit limits source target
  length_zero := by intros; rfl
  interactions := by intros; rfl

/-- The raw assertions check exactly the contract in both directions. -/
theorem checks_iff (limits : ResourceLimits) (source target : ExecutionSnapshot)
    (input : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    (checker limits source target).Checks input data ↔ Spec limits source target input := by
  have raw (vars : Var SP1PublicIO (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
      ((main limits source target vars).operations offset).ConstraintsHold env ↔
        Spec limits source target (eval env vars) := by
    by_cases valid : checkBounds limits source target = true
    · simp [main, circuit_norm, seval, valid, Spec,
        (checkBounds_iff limits source target).mp valid, ClockFor, sub_eq_zero]
    · have invalid := mt (checkBounds_iff limits source target).mpr valid
      simp [main, circuit_norm, seval, valid, Spec, invalid]
  exact (raw (varFromOffset SP1PublicIO 0) (size SP1PublicIO) (Environment.fromInput input data)).trans
    (by rw [ProvableType.eval_fromInput_varFromOffset_zero])

end SP1Clean.ResourceBoundary
