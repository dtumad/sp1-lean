import SP1Clean.FormalModel.Contracts.WriteSlice
import ToClean.Air.StaticProvider

/-! # Fixed source for grouped WRITE alignment and lane selection

All legal windows, including empty selections, are small verifier-independent constants.
A precise byte selection can be generated from an authenticated address and payload interval.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat

variable {p : Nat} [Fact p.Prime]

/-- Fixed inventory of every legal guest interval and destination offset. -/
def planTable : StaticTable (ZMod p) SlicePlan := .ofRows "sp1.native.write_slice_plan" slicePlans

omit [Fact p.Prime] in
/-- The fixed plan inventory has 352 legal windows and occupies 512 physical rows. -/
theorem planTable_height : (planTable (p := p)).height = 512 := by
  have rows : (planTable (p := p)).length = 352 := by
    change (slicePlans (p := p)).length = 352
    simp only [slicePlans, List.length_flatMap, List.length_map, List.length_range]
    decide
  rw [StaticTable.height, rows]
  decide

omit [Fact p.Prime] in
private theorem plan_height : (planTable (p := p)).height < UInt64.size := by rw [planTable_height]; decide

/-- Preallocated provider of lane masks for grouped word placement. -/
def planComponent : Component (ZMod p) :=
  planTable.payloadComponent sliceChannel (by intros; trivial) plan_height

theorem plan_authenticates (table : Table (ZMod p)) (installed : table.component = planComponent) (checked : table.Constraints) :
    table.Authenticates sliceChannel fun plan =>
      ∃ first size offset, first < 8 ∧ first + size ≤ 8 ∧ offset < 8 ∧ plan = .ofNat first size offset := by
  apply (planTable.payload_authenticates sliceChannel (by intros; trivial) plan_height table installed checked).mono
  exact fun _ member => (slicePlans_iff _).mp member

end SP1Clean.WriteEffects
