import SP1Clean.Native.Operations.AddOperation.Carries
import SP1Clean.Native.Operations.AddOperation.Populate
import SP1Clean.Native.Operations.AddOperation.Defs

/-! # `AddOperation` — the `FormalAssertion` (soundness / completeness / contract)

The bundled addition assertion connects each result-limb byte lookup to `Word.isU64`
and its four binary carries to addition modulo $2^{64}$. -/

namespace SP1Clean.AddOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- On a real row (`is_real = 1`) the operand words fit in 64 bits, and `is_real` is binary (the latter
discharged by the composing chip's `is_real * (is_real - 1) = 0` gate). The `isU64` precondition is **gated
on `is_real`**: a padding row owes nothing, so a chip feeding a *witnessed* operand (whose range check
is itself `is_real`-gated, e.g. DivRem's `abs_remainder`) can still discharge this assumption. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b) ∧ (input.is_real = 0 ∨ input.is_real = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3, _hbool, hgc0, hgc1, hgc2, hgc3⟩ := h_holds
  -- The four trailing conjuncts are the limb byte pulls' own `Requirements` — vacuous off-gate (`cedc171b`).
  refine ⟨fun hr1eq => ?_, hbin⟩
  obtain ⟨ha, hb⟩ := hab_imp hr1eq
  have hneg : input_is_real = 1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [← c16] at R0 R1 R2 R3
  rw [hr1eq, one_mul] at hgc0 hgc1 hgc2 hgc3
  have bounded : Word.isU64 input_cols_value := Word.isU64_of_cases ((byteRowSpec_u16 _).mp R0)
    ((byteRowSpec_u16 _).mp R1) ((byteRowSpec_u16 _).mp R2)
    ((byteRowSpec_u16 _).mp R3)
  refine ⟨bounded, addSemantics_of_carries ha hb bounded ?_⟩
  intro i
  fin_cases i
  · exact IsBool.iff_mul_sub_one.mpr hgc0
  · exact IsBool.iff_mul_sub_one.mpr hgc1
  · exact IsBool.iff_mul_sub_one.mpr hgc2
  · exact IsBool.iff_mul_sub_one.mpr hgc3

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hab_imp, hbin⟩ := h_assumptions
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
  have key (hneg : input_is_real = 1) :=
    Word.lt_cases_of_isU64 (h_spec hneg).1
  simp only [circuit_norm, byteChannel]
  refine ⟨fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, fun hneg => ?_, ?_⟩
  · rw [← c16]; exact (byteRowSpec_u16 _).mpr (key hneg).1
  · rw [← c16]; exact (byteRowSpec_u16 _).mpr (key hneg).2.1
  · rw [← c16]; exact (byteRowSpec_u16 _).mpr (key hneg).2.2.1
  · rw [← c16]; exact (byteRowSpec_u16 _).mpr (key hneg).2.2.2
  · rcases hbin with h0 | h1
    · simp [h0]
    · obtain ⟨hv, hbv⟩ := h_spec h1
      obtain ⟨ha, hb⟩ := hab_imp h1
      have binary := carries_of_addSemantics ha hb hv hbv
      rw [h1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [one_mul]
        exact IsBool.iff_mul_sub_one.mp (binary 0)
      · rw [one_mul]
        exact IsBool.iff_mul_sub_one.mp (binary 1)
      · rw [one_mul]
        exact IsBool.iff_mul_sub_one.mp (binary 2)
      · rw [one_mul]
        exact IsBool.iff_mul_sub_one.mp (binary 3)

/-- The proof-oriented local addition gadget as a Clean-native `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := []
  requirementsChannelsLawful input_var i₀ := by
    preserve_tactic_target
    simp only [circuit_norm, main, byteChannel]
    intro env h_constraints
    exact bool_of_mul_pred h_constraints.1

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    circuit.channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.AddOperation
