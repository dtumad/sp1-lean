import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Semantics.Host.WriteDescriptor
import Clean.Gadgets.IsZeroField

/-! # Native WRITE descriptor dispatch

The low limb distinguishes the released descriptor codes. The next limb must vanish on every
recognized path; the upper pair must also vanish for stdout and stderr.
-/

namespace SP1Clean.WriteDescriptor
open Circuit Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The dispatch code is witnessed by the standard deterministic zero tests. -/
def main (w : Var Word (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  assertion WordRangeCheck.circuit w
  let mid ← Gadgets.IsZeroField.circuit w[1]
  let upper ← Gadgets.IsZeroField.circuit (w[2] + w[3])
  let lo : Expression (ZMod p) := w[0]
  let std <== (lo - 1) * (lo - 2)
  let stream ← Gadgets.IsZeroField.circuit std
  let pairA <== (lo - 13) * (lo - 14)
  let rootsA <== pairA * (lo - 15)
  let groupA ← Gadgets.IsZeroField.circuit rootsA
  let pairB <== (lo - 16) * (lo - 17)
  let rootsB <== pairB * (lo - 18)
  let groupB ← Gadgets.IsZeroField.circuit rootsB
  let pairC <== (lo - 19) * (lo - 20)
  let rootsC <== pairC * (lo - 21)
  let groupC ← Gadgets.IsZeroField.circuit rootsC
  let base <== lo * mid
  let standard <== upper * stream
  let route <== base * (standard + groupA + groupB + groupC)
  return route

instance elaborated : ElaboratedCircuit (ZMod p) Word field main := by elaborate_circuit

private theorem val_eq_cast {x : ZMod p} {n : Nat} (small : n ≤ 21) :
    x = (n : ZMod p) ↔ x.val = n := by
  have hp : 2 ^ 17 < p := Fact.out
  have eq := ZMod.val_natCast_of_lt (show n < p by omega)
  exact ⟨fun h => (congrArg ZMod.val h).trans eq, fun h => ZMod.val_injective p (h.trans eq.symm)⟩

private theorem upper_zero (w : Word (ZMod p)) (bound : w.isU64) :
    w[2] + w[3] = 0 ↔ w[2].val = 0 ∧ w[3].val = 0 := by
  have hp : 2 ^ 17 < p := Fact.out
  have bounds := Word.lt_cases_of_isU64 bound
  rw [← ZMod.val_eq_zero, ZMod.val_add_of_lt (by omega), Nat.add_eq_zero_iff]

omit [Fact (2 ^ 17 < p)] in
private theorem low32 (w : Word (ZMod p)) (bound : w.isU64) :
    (w.toBitVec64.setWidth 32).toNat = w[0].val + 65536 * w[1].val := by
  rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat bound, Word.toNat_def]
  have bounds := Word.lt_cases_of_isU64 bound
  omega

omit [Fact (2 ^ 17 < p)] in
private theorem tag_of_limbs (w : Word (ZMod p)) (bound : w.isU64) :
    (WriteRoute.ofDescriptor w.toBitVec64).tag =
      if w[1].val = 0 then
        if (w[2].val = 0 ∧ w[3].val = 0) ∧ (w[0].val = 1 ∨ w[0].val = 2) then w[0].val
        else if 13 ≤ w[0].val ∧ w[0].val ≤ 21 then w[0].val else 0
      else 0 := by
  have full := Word.toBitVec64_toNat bound
  rw [Word.toNat_def] at full
  have low := low32 w bound
  have hooks : w.toBitVec64.setWidth 32 ∈ hookDescriptors ↔
      15 ≤ (w.toBitVec64.setWidth 32).toNat ∧ (w.toBitVec64.setWidth 32).toNat ≤ 21 := by
    simp only [hookDescriptors, List.mem_cons, List.not_mem_nil, or_false, ← BitVec.toNat_inj]
    change _ = 15 ∨ _ = 16 ∨ _ = 17 ∨ _ = 18 ∨ _ = 19 ∨ _ = 20 ∨ _ = 21 ↔ _
    omega
  simp only [WriteRoute.ofDescriptor, hooks, ← BitVec.toNat_inj]
  change (if w.toBitVec64.toNat = 1 then WriteRoute.stdout else
    if w.toBitVec64.toNat = 2 then .stderr else
    if (w.toBitVec64.setWidth 32).toNat = 13 then .publicValues else
    if (w.toBitVec64.setWidth 32).toNat = 14 then .hint else
    if _ then .hook _ else .ignored).tag = _
  split_ifs <;> simp only [WriteRoute.tag] <;> omega

private theorem route_value (input : Word (ZMod p)) (bound : input.isU64) :
    input[0] * (if input[1] = 0 then 1 else 0) *
      ((if input[2] + input[3] = 0 then 1 else 0) *
          (if (input[0] - (1 : ZMod p))*(input[0] - (2 : ZMod p)) = 0 then 1 else 0) +
        (if (input[0] - (13 : ZMod p))*(input[0] - (14 : ZMod p))*(input[0] - (15 : ZMod p)) = 0 then 1 else 0) +
        (if (input[0] - (16 : ZMod p))*(input[0] - (17 : ZMod p))*(input[0] - (18 : ZMod p)) = 0 then 1 else 0) +
        (if (input[0] - (19 : ZMod p))*(input[0] - (20 : ZMod p))*(input[0] - (21 : ZMod p)) = 0 then 1 else 0)) =
      ((WriteRoute.ofDescriptor input.toBitVec64).tag : ZMod p) := by
  rw [tag_of_limbs input bound]
  simp only [mul_eq_zero, sub_eq_zero, upper_zero input bound]
  simp only [(ZMod.val_eq_zero (input[1])).symm]
  have scalar (n : Nat) (small : n ≤ 21) := val_eq_cast (p := p) (x := input[0]) small
  have e1 : input[0] = (1 : ZMod p) ↔ input[0].val = 1 := by simpa only [Nat.cast_one] using scalar 1 (by decide)
  have e2 : input[0] = (2 : ZMod p) ↔ input[0].val = 2 := scalar 2 (by decide)
  have e13 : input[0] = (13 : ZMod p) ↔ input[0].val = 13 := scalar 13 (by decide)
  have e14 : input[0] = (14 : ZMod p) ↔ input[0].val = 14 := scalar 14 (by decide)
  have e15 : input[0] = (15 : ZMod p) ↔ input[0].val = 15 := scalar 15 (by decide)
  have e16 : input[0] = (16 : ZMod p) ↔ input[0].val = 16 := scalar 16 (by decide)
  have e17 : input[0] = (17 : ZMod p) ↔ input[0].val = 17 := scalar 17 (by decide)
  have e18 : input[0] = (18 : ZMod p) ↔ input[0].val = 18 := scalar 18 (by decide)
  have e19 : input[0] = (19 : ZMod p) ↔ input[0].val = 19 := scalar 19 (by decide)
  have e20 : input[0] = (20 : ZMod p) ↔ input[0].val = 20 := scalar 20 (by decide)
  have e21 : input[0] = (21 : ZMod p) ↔ input[0].val = 21 := scalar 21 (by decide)
  simp only [e1, e2, e13, e14, e15, e16, e17, e18, e19, e20, e21]
  by_cases mid : input[1].val = 0
  · simp only [mid, ite_true, mul_one]
    by_cases high : input[2].val = 0 ∧ input[3].val = 0
    all_goals simp only [high, ite_true, ite_false, true_and, false_and, one_mul, zero_mul, zero_add]
    all_goals
      split_ifs <;> simp only [add_zero, zero_add, mul_one, mul_zero, Nat.cast_zero,
        ZMod.natCast_zmod_val] <;> exfalso <;> omega
  · simp [mid]

/-- Range checking rejects malformed limbs, and the computed field is the unique released route tag. -/
def circuit : GeneralFormalCircuit (ZMod p) Word field where
  name := "sp1.native.write_descriptor"
  main
  elaborated
  computableWitnesses := by computable_witnesses
  Spec w route _ := w.isU64 ∧ route = ((WriteRoute.ofDescriptor w.toBitVec64).tag : ZMod p)
  ProverAssumptions w _ _ := w.isU64
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions,
      WordRangeCheck.Spec, Gadgets.IsZeroField.circuit]
    obtain ⟨bound, mid, upper, std, stream, a, ra, ga, b, rb, gb, c, rc, gc, base, standard, route⟩ := h_holds
    refine ⟨bound, ?_⟩
    simpa only [route, base, standard, mid, upper, stream, std, ga, ra, a, gb, rb, b, gc, rc, c]
      using route_value input bound
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions,
      WordRangeCheck.Spec, Gadgets.IsZeroField.circuit]
    obtain ⟨_, _, std, _, a, ra, _, b, rb, _, c, rc, _, base, standard, route⟩ := h_env
    exact ⟨h_assumptions, std, a, ra, b, rb, c, rc, base, standard, route⟩

end SP1Clean.WriteDescriptor
