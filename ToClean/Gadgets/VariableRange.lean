module

public import Clean.Gadgets.Bits
public import ToClean.Circuit.ExpressionSum
public import ToClean.Gadgets.LookupProjection

/-! # Variable-width unsigned range checks

Missing upstream capability: a bundled range assertion whose width is a circuit input.
The value uses Clean's bit decomposition; a boolean prefix mask selects the allowed bits.
Both witnesses use the standard witness IR and export through Clean's built-in backends.
Move this gadget upstream and delete the local addition when Clean supplies this interface.
-/

@[expose] public section

namespace Gadgets.VariableRange

open Circuit Utils.Bits

variable {p : ℕ} [Fact p.Prime]

private theorem prefix_of_constraints {n : ℕ} (mask : Fin n → F p)
    (hbool : ∀ i, IsBool (mask i))
    (hstep : ∀ i : Fin (n - 1),
      mask ⟨i.val + 1, by omega⟩ * (1 - mask ⟨i.val, by omega⟩) = 0) :
    ∃ k ≤ n, ∀ i, mask i = if i.val < k then 1 else 0 := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    rcases hbool 0 with hzero | hone
    · refine ⟨0, Nat.zero_le _, ?_⟩
      intro i
      suffices ∀ j (hj : j < n + 1), mask ⟨j, hj⟩ = 0 by simpa using this i.val i.isLt
      intro j
      induction j with
      | zero => intro _; exact hzero
      | succ j hj =>
        intro hbound
        have hs := hstep ⟨j, by omega⟩
        simpa [hj (by omega)] using hs
    · obtain ⟨k, hk, hmask⟩ := ih (fun i => mask i.succ) (fun i => hbool i.succ)
        (fun i => hstep ⟨i.val + 1, by omega⟩)
      refine ⟨k + 1, by omega, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hone
      · simpa using hmask j

private theorem sum_prefix {n k : ℕ} (hk : k ≤ n) :
    (∑ i : Fin n, if i.val < k then (1 : F p) else 0) = k := by
  induction n generalizing k with
  | zero => simp_all
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    cases k with
    | zero => simp
    | succ k =>
      simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ,
        Nat.add_lt_add_iff_right]
      rw [ih (by omega), Nat.cast_add, Nat.cast_one, add_comm]

private theorem range_of_mask {n : ℕ} (hn : 2 ^ n < p) (x width : F p)
    (mask : Fin n → F p) (hx : x.val < 2 ^ n)
    (hbool : ∀ i, IsBool (mask i))
    (hstep : ∀ i : Fin (n - 1),
      mask ⟨i.val + 1, by omega⟩ * (1 - mask ⟨i.val, by omega⟩) = 0)
    (hsum : width = ∑ i, mask i)
    (hzero : ∀ i : Fin n, (fieldToBits n x)[i] * (1 - mask i) = 0) :
    width.val ≤ n ∧ x.val < 2 ^ width.val := by
  obtain ⟨k, hk, hmask⟩ := prefix_of_constraints mask hbool hstep
  have hwidth : width.val = k := by
    rw [hsum, Finset.sum_congr rfl (fun i _ => hmask i), sum_prefix hk,
      ZMod.val_natCast_of_lt (lt_of_le_of_lt hk (lt_trans Nat.lt_two_pow_self hn))]
  rw [hwidth]
  refine ⟨hk, Nat.lt_pow_two_of_testBit _ fun i hi => ?_⟩
  by_cases hin : i < n
  · have hz := hzero ⟨i, hin⟩
    rw [hmask] at hz
    simp only [show ¬ i < k by omega, ↓reduceIte, sub_zero, mul_one] at hz
    cases hbit : x.val.testBit i
    · rfl
    · simp [Fin.getElem_fin, fieldToBits, Utils.Bits.toBits, Vector.getElem_mapRange, hbit] at hz
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))

variable [Fact (p > 2)]

/-- Decompose the value and constrain a boolean prefix mask of its permitted bits. -/
def main (n : ℕ) (hn : 2 ^ n < p) (input : Var fieldPair (F p)) :
    Circuit (F p) Unit := do
  let bits ← ToBits.toBits n hn input.1
  let mask ← witnessVector n (.lit (.ofFn fun i =>
    .ite (.flt (.const (i.val : F p)) (.expr input.2)) 1 0))
  Circuit.forEach mask assertBool
  Circuit.forEach (Vector.ofFn fun i : Fin (n - 1) =>
    mask[i.val + 1] * (1 - mask[i.val])) assertZero
  input.2 === Expression.sum mask
  Circuit.forEach (Vector.ofFn fun i : Fin n => bits[i] * (1 - mask[i])) assertZero

/-- An unsigned bound with a runtime width, bounded by the fixed maximum `n`. -/
def rangeCheck (n : ℕ) (hn : 2 ^ n < p) : FormalAssertion (F p) fieldPair where
  main := main n hn
  Spec input := input.2.val ≤ n ∧ input.1.val < 2 ^ input.2.val
  soundness := by
    circuit_proof_start [ToBits.toBits]
    cases h_input
    obtain ⟨⟨hx, hbits⟩, hbool, hstep, hsum, hzero⟩ := h_holds
    apply range_of_mask hn _ _ _ hx hbool hstep hsum
    intro i
    rw [← hbits]
    simpa only [circuit_norm] using hzero i
  completeness := by
    circuit_proof_start [ToBits.toBits]
    cases h_input
    obtain ⟨hwidth, hx⟩ := h_spec
    have hxn := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hwidth)
    obtain ⟨hbits, hmask, _⟩ := h_env
    have hmask' (i : Fin n) : env.get (i₀ + n + i.val) =
        if i.val < (env input_var.2).val then 1 else 0 := by
      simpa only [decide_eq_true_eq, ZMod.val_natCast_of_lt
        (lt_trans i.isLt (lt_trans Nat.lt_two_pow_self hn))] using hmask i
    refine ⟨hxn, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [hmask' i]
      split <;> simp [IsBool]
    · intro i
      rw [hmask' ⟨i.val + 1, by omega⟩, hmask' ⟨i.val, by omega⟩]
      split <;> split <;> simp_all
      omega
    · simp_rw [hmask']
      rw [sum_prefix hwidth, ZMod.natCast_zmod_val]
    · intro i
      rw [hmask']
      split
      · simp
      · rename_i hi
        have hbit := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
            (by omega : (env input_var.2).val ≤ i.val)))
        have heq := congrArg (fun v : Vector (F p) n => v[i]) (hbits hxn).2
        simpa [fieldToBits, Utils.Bits.toBits, hbit, circuit_norm] using heq

end Gadgets.VariableRange
