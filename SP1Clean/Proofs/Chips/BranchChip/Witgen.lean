import SP1Clean.Proofs.Chips.BranchChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable branch witnesses

Clean generates the comparison from the operands and selectors, then the branch decision,
then the selected next PC. Every same-row read uses an earlier witness cell.
-/

namespace SP1Clean.BranchChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Branch's row has computable witnesses. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · -- Comparison certificate from ordinary inputs.
    refine LtOperationSigned.populateFE_congr_flat env env' _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_adapter h_input]
    · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_adapter h_input]
    · simp only [circuit_norm]
      rw [Inputs.eval_congr_isBlt h_input, Inputs.eval_congr_isBge h_input]
    · simpa only [eval_isReal] using congrArg Inputs.is_real h_input
  · -- Decision from selectors and the comparison cells already written.
    simp only [branchDecision, circuit_norm]
    rw [Inputs.eval_congr_isBeq h_input, Inputs.eval_congr_isBne h_input,
      Inputs.eval_congr_isBlt h_input, Inputs.eval_congr_isBge h_input,
      Inputs.eval_congr_isBltu h_input, Inputs.eval_congr_isBgeu h_input,
      h_agree.get_eq (i := n) (by omega),
      h_agree.get_eq (i := n + 1) (by omega),
      h_agree.get_eq (i := n + 1 + 1) (by omega),
      h_agree.get_eq (i := n + 1 + 2) (by omega),
      h_agree.get_eq (i := n + 1 + 3) (by omega)]
  · -- The three `next_pc` cells: pc/imm inputs, the `is_branching` cell below, `is_real`.
    refine nextPcIR_congr env env' _ _ _ _ (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_state h_input]
    · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_adapter h_input]
    · simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
    · simpa only [eval_isReal] using congrArg Inputs.is_real h_input
  all_goals simp [circuit_norm]

end SP1Clean.BranchChip
