module

public import Clean.Air.WitnessGeneration

/-! # Demand-generated table height bounds

Clean computes each table's target height and appends the missing rows. These lemmas expose the
same computation on a natural active count, including the empty table, and bound its result for
constructors which must supply a physical row-index bound.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration

/-- Physical height of a demand-generated table with this many active rows. -/
def demandHeight (active : ℕ) : ℕ := if active = 0 then 0 else nextPowerOfTwo active

/-- Number of rows appended by demand padding. -/
def demandPadding (active : ℕ) : ℕ := demandHeight active - active

theorem ComponentState.targetHeight_of_demand {F : Type} [FiniteField F] (state : ComponentState F)
    {mode} (generation : state.component.generation = .demand mode) :
    state.targetHeight = demandHeight state.rows.size := by
  simp [ComponentState.targetHeight, generation, demandHeight, Array.isEmpty]

private theorem nextPowerOfTwoAux_bounds (target fuel power : ℕ) (positive : 0 < power)
    (enough : target ≤ power + fuel) (upper : power ≤ 2 * target) :
    target ≤ nextPowerOfTwoAux target fuel power ∧ nextPowerOfTwoAux target fuel power ≤ 2 * target := by
  induction fuel generalizing power with
  | zero => simpa only [nextPowerOfTwoAux] using And.intro (by omega : target ≤ power) upper
  | succ fuel ih =>
    rw [nextPowerOfTwoAux]
    split
    · exact ⟨by assumption, upper⟩
    · apply ih <;> omega

private theorem nextPowerOfTwoAux_le_pow {target exponent : ℕ} (targetBound : target ≤ 2 ^ exponent)
    (fuel degree : ℕ) (current : degree ≤ exponent) : nextPowerOfTwoAux target fuel (2 ^ degree) ≤ 2 ^ exponent := by
  induction fuel generalizing degree with
  | zero => exact Nat.pow_le_pow_right (by decide : 0 < 2) current
  | succ fuel ih =>
    rw [nextPowerOfTwoAux]
    split
    · exact Nat.pow_le_pow_right (by decide : 0 < 2) current
    · rename_i below
      have strict : degree < exponent := by
        apply Nat.lt_of_le_of_ne current
        rintro rfl
        exact below targetBound
      rw [← Nat.pow_succ]
      exact ih _ strict

/-- Independently rounding one demand bucket respects any power-of-two ceiling on its
active count, including the empty bucket. -/
theorem demandHeight_le_pow {active exponent : ℕ} (bound : active ≤ 2 ^ exponent) :
    demandHeight active ≤ 2 ^ exponent := by
  unfold demandHeight
  split
  · exact Nat.zero_le _
  · simpa only [nextPowerOfTwo, Nat.max_eq_left (by omega : 1 ≤ active), Nat.pow_zero] using
      nextPowerOfTwoAux_le_pow bound active 0 (Nat.zero_le _)

theorem demandHeight_bounds (active : ℕ) : active ≤ demandHeight active ∧ demandHeight active ≤ 2 * active := by
  unfold demandHeight
  split
  · omega
  · simpa only [nextPowerOfTwo, Nat.max_eq_left (by omega : 1 ≤ active)] using
      nextPowerOfTwoAux_bounds active active 1 (by decide) (by omega) (by omega)

theorem add_demandPadding (active : ℕ) : active + demandPadding active = demandHeight active := by
  have bounds := demandHeight_bounds active
  unfold demandPadding
  omega

end Air.Flat.WitnessGeneration
