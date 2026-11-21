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
