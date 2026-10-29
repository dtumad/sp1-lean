module

public import Clean.Gadgets.Equality
public import ToClean.Circuit.ExpressionSum
public import ToClean.Gadgets.LookupProjection

/-! # One-hot decoding of a bounded field index

Missing upstream capability: a bundled one-hot decoder using the standard witness IR.
Each selector gates an equality between the input and its index; their sum is one. Distinct
indices force exactly one selector to be one, without separate boolean constraints. Move
this gadget upstream when Clean supplies this interface.
-/

@[expose] public section

namespace Gadgets.OneHot

open Circuit

variable {p : ℕ} [Fact p.Prime]

private theorem decode {n : ℕ} (hn : n ≤ p) (x : F p) (s : Fin n → F p)
    (hg : ∀ i, s i * (x - (i.val : F p)) = 0) (hs : (∑ i, s i) = 1) :
    x.val < n ∧ ∀ i, s i = if x.val = i.val then 1 else 0 := by
  have hs0 (i : Fin n) (hi : x ≠ (i.val : F p)) : s i = 0 :=
    (mul_eq_zero.mp (hg i)).resolve_right (sub_ne_zero.mpr hi)
  have hex : ∃ i : Fin n, x = (i.val : F p) := by
    by_contra h
    push Not at h
    have hz : ∀ i, s i = 0 := fun i => hs0 i (h i)
    simp [hz] at hs
  obtain ⟨k, hk⟩ := hex
  have hx : x.val = k.val := by rw [hk, ZMod.val_natCast_of_lt (lt_of_lt_of_le k.isLt hn)]
  have hother (i : Fin n) (hi : i ≠ k) : s i = 0 := by
    apply hs0
    intro heq
    have hv := congrArg ZMod.val heq
    rw [hx, ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hn)] at hv
    exact hi (Fin.ext hv.symm)
  have hsk : s k = 1 := by
    rwa [Finset.sum_eq_single k (fun i _ hi => hother i hi) (by simp)] at hs
  refine ⟨hx ▸ k.isLt, fun i => ?_⟩
  by_cases hi : i = k
  · subst i; simp [hx, hsk]
  · have hv : k.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [hx, hv, hother i hi]

/-- Witness one selector per possible input and constrain the unique selected index. -/
def main (n : ℕ) (x : Expression (F p)) : Circuit (F p) (Var (fields n) (F p)) := do
  let s ← witnessVector n (.lit (.ofFn fun i =>
    .ite (.feq (.expr x) (.const (i.val : F p))) 1 0))
  Circuit.forEach (Vector.ofFn fun i : Fin n => s[i] * (x - .const (i.val : F p))) assertZero
  Expression.sum s === 1
  return s

/-- Decode an index into one-hot selectors, proving both the bound and the full output vector. -/
def circuit (n : ℕ) (hn : n ≤ p) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n
  Spec input output _ := input.val < n ∧
    output = .ofFn (fun i => if input.val = i.val then 1 else 0)
  ProverAssumptions input _ _ := input.val < n
  soundness := by
    circuit_proof_start
    cases h_input
    obtain ⟨hgate, hsum⟩ := h_holds
    obtain ⟨hx, hs⟩ := decode hn _ _ hgate hsum
    refine ⟨hx, ?_⟩
    ext i hi
    simpa only [circuit_norm] using hs ⟨i, hi⟩
  completeness := by
    circuit_proof_start
    cases h_input
    have hw := h_env
    have hw' (i : Fin n) : env.get (i₀ + i.val) =
        if (env input_var).val = i.val then 1 else 0 := by
      have heq : env input_var = (i.val : F p) ↔ (env input_var).val = i.val := by
        constructor
        · intro h; rw [h, ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hn)]
        · intro h; rw [← h, ZMod.natCast_zmod_val]
      simpa only [heq] using hw i
    constructor
    · intro i
      rw [hw' i]
      split
      · rename_i hi
        have heq : env input_var = (i.val : F p) := by rw [← hi, ZMod.natCast_zmod_val]
        simp [heq]
      · simp
    · simp_rw [hw']
      let k : Fin n := ⟨(env input_var).val, h_assumptions⟩
      change (∑ i : Fin n, if k.val = i.val then (1 : F p) else 0) = 1
      simp only [← Fin.ext_iff]
      simp

end Gadgets.OneHot
