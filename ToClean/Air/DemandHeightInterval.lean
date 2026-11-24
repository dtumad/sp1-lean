module

public import ToClean.Air.DemandPadding

/-! # Exact demand heights between consecutive powers of two

Clean exposes its demand scheduler's height function. These lemmas identify its positive
range and give both directions of the rounding criterion for capacity proofs.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration

private theorem aux_power (target fuel degree : Nat) :
    ∃ exponent : Nat, nextPowerOfTwoAux target fuel (2 ^ degree) = 2 ^ exponent := by
  induction fuel generalizing degree with
  | zero => exact ⟨degree,rfl⟩
  | succ fuel ih =>
    rw [nextPowerOfTwoAux]
    split
    · exact ⟨degree,rfl⟩
    · rw [← Nat.pow_succ]
      exact ih _

/-- A nonempty demand table always has power-of-two height. -/
theorem demandHeight_power {active : Nat} (positive : active ≠ 0) :
    ∃ exponent : Nat, demandHeight active = 2 ^ exponent := by
  rw [demandHeight,ite_eq_right positive,nextPowerOfTwo]
  exact aux_power _ _ 0

/-- The full power-of-two ceiling is reached whenever the raw row count is strictly
above the preceding power of two, including the upper equality. -/
theorem demandHeight_of_interval {active exponent : Nat} (above : 2 ^ exponent < active)
    (within : active ≤ 2 ^ (exponent+1)) : demandHeight active = 2 ^ (exponent+1) := by
  have positive : active ≠ 0 := by omega
  obtain ⟨k,height⟩ := demandHeight_power positive
  have lo := above.trans_le (demandHeight_bounds active).1
  have hi := demandHeight_le_pow within
  rw [height,Nat.pow_lt_pow_iff_right (by decide)] at lo
  rw [height,Nat.pow_le_pow_iff_right (by decide)] at hi
  have eq : k = exponent+1 := by omega
  rw [height,eq]

end Air.Flat.WitnessGeneration
