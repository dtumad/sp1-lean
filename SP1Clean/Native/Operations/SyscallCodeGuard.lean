import SP1Clean.FormalModel.Contracts.CoreSyscall
import ToClean.Circuit.SubcircuitProjection
import Clean.Gadgets.Equality
import Clean.Utils.Tactics

/-! # Canonical native syscall words without a lookup

The eight permitted low limbs are roots of a polynomial. Six shared products keep every AIR
constraint at degree at most three, and active rows must have zero upper limbs. The boolean gate
leaves padding unconstrained. Clean supplies witness generation and Rust lowering directly;
there is no fixed provider or channel assumption at this boundary.
-/

namespace SP1Clean.SyscallCodeGuard

open Circuit Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem canonical_iff (word : Word (ZMod p)) :
    word.isU64 ∧ SyscallKind.Supported word.toBitVec64 ↔
      (word[0] = 0 ∨ word[0] = 2 ∨ word[0] = 3 ∨ word[0] = 16 ∨
        word[0] = 26 ∨ word[0] = 27 ∨ word[0] = 240 ∨ word[0] = 241) ∧
      word[1] = 0 ∧ word[2] = 0 ∧ word[3] = 0 := by
  rw [← SyscallKind.mem_encoded_iff]
  have eta : word = #v[word[0], word[1], word[2], word[3]] := by
    ext i hi
    interval_cases i <;> rfl
  rw [eta]
  simp [SyscallKind.all, SyscallKind.encode, SyscallKind.code, Soundness.Target.bitVecToWord,
    Array.mk.injEq]
  tauto

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.is_real * (input.is_real - 1))
  let x := input.code[0]
  let p2 <== x * (x - 2)
  let p3 <== p2 * (x - 3)
  let p4 <== p3 * (x - 16)
  let p5 <== p4 * (x - 26)
  let p6 <== p5 * (x - 27)
  let p7 <== p6 * (x - 240)
  assertZero (input.is_real * (p7 * (x - 241)))
  assertZero (input.is_real * input.code[1])
  assertZero (input.is_real * input.code[2])
  assertZero (input.is_real * input.code[3])

omit [Fact (2 ^ 17 < p)] in
/-- The guard introduces no ledger occurrences. -/
@[circuit_norm] theorem main_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactions = [] := by
  simp [main, circuit_norm, FormalAssertion.toSubcircuit_interactions,
    Gadgets.Equality.circuit, Gadgets.Equality.main]

omit [Fact (2 ^ 17 < p)] in
/-- Every check lowers directly to arithmetic AIR. -/
@[circuit_norm] theorem main_lookups (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).lookups = [] := by
  simp [main, circuit_norm, Gadgets.Equality.circuit, Gadgets.Equality.main]

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 6
  output _ _ := ()
  channelsWithGuarantees := []

theorem soundness : FormalAssertion.Soundness (ZMod p) main (fun _ => True) Spec := by
  circuit_proof_start [Spec]
  obtain ⟨binary, h2, h3, h4, h5, h6, h7, low, high1, high2, high3⟩ := h_holds
  refine ⟨?_, ?_⟩
  · simpa only [mul_eq_zero, sub_eq_zero] using binary
  · intro real
    apply (canonical_iff _).mpr
    rw [← h_input.1]
    simp only [Vector.getElem_map]
    simp only [h7, h6, h5, h4, h3, h2, real, one_mul, mul_eq_zero, sub_eq_zero]
      at low high1 high2 high3
    exact ⟨by tauto, high1, high2, high3⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main (fun _ => True) Spec := by
  circuit_proof_start [Spec]
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ := h_env
  simp only [h7, h6, h5, h4, h3, h2]
  obtain ⟨binary, valid⟩ := h_spec
  rcases binary with zero | one
  · simp [zero]
  · have canonical := (canonical_iff _).mp (valid one)
    rw [← h_input.1] at canonical
    simp only [Vector.getElem_map] at canonical
    simp only [one, sub_self, mul_zero, one_mul, mul_eq_zero, sub_eq_zero]
    tauto

def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated, Assumptions := fun _ => True, Spec, soundness, completeness }

end SP1Clean.SyscallCodeGuard
