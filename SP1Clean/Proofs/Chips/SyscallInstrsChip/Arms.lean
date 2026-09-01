import SP1Clean.Native.Chips.SyscallInstrsChip.Arms
import Clean.Utils.Tactics

/-! # The `SyscallInstrs` arms' soundness and completeness

One bundled `FormalAssertion` per arm. Each proof sees only the constraints of its own arm, which
is the whole point of the decomposition — see the module docstring of
`Native/Chips/SyscallInstrsChip/Arms.lean`. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- A gated constraint holds when the gate is boolean and the gated fact holds on a live gate. -/
private lemma gate_zero {x y : ZMod p}
    (hx : x = 0 ∨ x = 1) (h : x = 1 → y = 0) : x * y = 0 := by
  rcases hx with h0 | h1
  · rw [h0]; ring
  · rw [h1, one_mul]; exact h h1

omit [Fact (2 ^ 17 < p)] in
private lemma one_sub_bool {x : ZMod p}
    (hx : x = 0 ∨ x = 1) : (1 : ZMod p) - x = 0 ∨ (1 : ZMod p) - x = 1 := by
  rcases hx with h | h <;> rw [h] <;> simp

omit [Fact (2 ^ 17 < p)] in
private lemma eq_zero_of_one_sub {x : ZMod p}
    (h : (1 : ZMod p) - x = 1) : x = 0 := by linear_combination -h

namespace PcArm

omit [Fact (2 ^ 17 < p)] in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_hbin⟩ := h_assumptions
  obtain ⟨e0, e1, e2, h0, h1, h2⟩ := h_holds
  have epc : ∀ i (hi : i < 3),
      Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have enp : ∀ i (hi : i < 3),
      Expression.eval env input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  rw [enp 0 (by norm_num)] at e0 h0
  rw [enp 1 (by norm_num)] at e1 h1
  rw [enp 2 (by norm_num)] at e2 h2
  rw [epc 0 (by norm_num)] at e0
  rw [epc 1 (by norm_num)] at e1
  rw [epc 2 (by norm_num)] at e2
  refine ⟨fun hh => ?_, fun hr hnh => ?_⟩
  · rw [hh, one_mul] at h0 h1 h2
    exact ⟨by linear_combination h0, h1, h2⟩
  · rw [hr, one_mul, hnh] at e0 e1 e2
    simp only [sub_zero, one_mul] at e0 e1 e2
    exact ⟨by linear_combination e0, by linear_combination e1, by linear_combination e2⟩

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_rbin, h_hbin⟩ := h_assumptions
  obtain ⟨h_halt, h_next⟩ := h_spec
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1; simpa using this
  have enp : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_next_pc[i] = input_next_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.1; simpa using this
  simp only [epc, enp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).2.1))
  · exact gate_zero h_rbin (fun hr => gate_zero (one_sub_bool h_hbin)
      (fun hg => by linear_combination (h_next hr (eq_zero_of_one_sub hg)).2.2))
  · exact gate_zero h_hbin (fun hh => by linear_combination (h_halt hh).1)
  · exact gate_zero h_hbin (fun hh => (h_halt hh).2.1)
  · exact gate_zero h_hbin (fun hh => (h_halt hh).2.2)

/-- The program-counter arm as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end PcArm

end SP1Clean.SyscallInstrsChip
