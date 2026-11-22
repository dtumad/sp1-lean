import SP1Clean.Proofs.Completeness.MixedStateSchedule

/-! # StateBump carry boundaries for an eight-tick fall-through

Each case uses the raw State message produced by an ordinary fall-through. The positive
cases record the exact normalized limbs. The two overflow cases isolate the failed limb.
-/

namespace SP1CleanTest.MixedStateBumpEdges

open SP1Clean.TraceGen

/-- A low PC carry can fill the middle limb while both upper limbs are already maximal. -/
theorem low_pc_carry_at_full_upper_limbs :
    let raw := StateRecord.fallThrough (2 ^ 48 - 2 ^ 24 + 1) (2 ^ 48 - 2 ^ 16 - 4) 8
    raw = ⟨2 ^ 24 - 1, 9, 2 ^ 16, 2 ^ 16 - 2, 2 ^ 16 - 1⟩ ∧
      raw.normalize = ⟨2 ^ 24 - 1, 9, 0, 2 ^ 16 - 1, 2 ^ 16 - 1⟩ ∧
      raw.toBumpEvent.WellFormed := by
  refine ⟨rfl, rfl, ?_⟩
  exact (StateRecord.fallThrough_valid (by decide) (by decide) (by decide) (by decide)).1

/-- The last legal clock-window carry fills the clock high limb while the PC top limb is full. -/
theorem clock_carry_into_last_window :
    let raw := StateRecord.fallThrough (2 ^ 48 - 2 ^ 24 - 7) (2 ^ 48 - 8) 8
    raw.toBumpEvent.isClk = 1 ∧
      raw.normalize = ⟨2 ^ 24 - 1, 1, 2 ^ 16 - 4, 2 ^ 16 - 1, 2 ^ 16 - 1⟩ ∧
      raw.toBumpEvent.WellFormed := by
  refine ⟨rfl, rfl, ?_⟩
  exact (StateRecord.fallThrough_valid (by decide) (by decide) (by decide) (by decide)).1

/-- A carry through both low PC limbs may fill the top limb while the clock high limb is full. -/
theorem pc_carry_into_last_top_limb :
    let raw := StateRecord.fallThrough (2 ^ 48 - 2 ^ 24 + 1) (2 ^ 48 - 2 ^ 32 - 4) 8
    raw.toBumpEvent.b1 = 1 ∧ raw.normalize = ⟨2 ^ 24 - 1, 9, 0, 0, 2 ^ 16 - 1⟩ ∧
      raw.toBumpEvent.WellFormed := by
  refine ⟨rfl, rfl, ?_⟩
  exact (StateRecord.fallThrough_valid (by decide) (by decide) (by decide) (by decide)).1

/-- A clock-window carry into an already full clock high limb exceeds the 48-bit clock. -/
theorem clock_carry_past_last_window :
    let raw := StateRecord.fallThrough (2 ^ 48 - 7) (2 ^ 48 - 8) 8
    raw.toBumpEvent.nextClkHigh = 2 ^ 24 ∧ ¬raw.toBumpEvent.WellFormed := by
  refine ⟨rfl, fun valid => ?_⟩
  exact (Nat.lt_irrefl (2 ^ 24)) valid.clkHigh

/-- A carry through both low PC limbs into an already full top limb exceeds the 48-bit PC. -/
theorem pc_carry_past_last_top_limb :
    let raw := StateRecord.fallThrough (2 ^ 48 - 2 ^ 24 + 1) (2 ^ 48 - 4) 8
    raw.toBumpEvent.nextPc2 = 2 ^ 16 ∧ ¬raw.toBumpEvent.WellFormed := by
  refine ⟨rfl, fun valid => ?_⟩
  exact (Nat.lt_irrefl (2 ^ 16)) valid.pc2

end SP1CleanTest.MixedStateBumpEdges
