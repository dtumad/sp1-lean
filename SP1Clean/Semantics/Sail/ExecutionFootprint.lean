module

public import SP1Clean.Semantics.Sail.Register

/-! # Register and simulator fields preserved by native instruction execution -/

@[expose] public section

namespace SP1Clean.Semantics
open LeanRV64D

namespace SailSnapshot

/-- The registers whose values can change along a supported native execution. -/
def executionRegister (reg : Register) : Bool :=
  decide (reg = .PC ∨ reg = .nextPC ∨ reg = .minstret ∨ reg = .minstret_increment ∨ reg = .mip ∨ reg = .written_event_index ∨
    ∃ index : BitVec 5, index ≠ 0 ∧ reg = reg_idx_to_Register index)

end SailSnapshot

/-- Exact preservation includes absent register entries and both simulator fields. -/
structure SailFrame (fixed : Register → Prop) (source target : SailState) : Prop where
  registers : ∀ reg, fixed reg → target.regs.get? reg = source.regs.get? reg
  cycles : target.cycleCount = source.cycleCount
  output : target.sailOutput = source.sailOutput

theorem SailFrame.refl {fixed : Register → Prop} (state : SailState) : SailFrame fixed state state :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem SailFrame.trans {fixed : Register → Prop} {a b c : SailState}
    (first : SailFrame fixed a b) (second : SailFrame fixed b c) : SailFrame fixed a c :=
  ⟨fun reg h => (second.registers reg h).trans (first.registers reg h),
    second.cycles.trans first.cycles, second.output.trans first.output⟩

/-- The decoded execute stage can stage a successor and write a nonzero destination GPR. -/
abbrev ExecuteFrame := SailFrame (fun reg => reg ≠ .nextPC ∧
  ∀ index : BitVec 5, index ≠ 0 → reg ≠ reg_idx_to_Register index)

/-- The complete transition also includes the official prelude and retirement writes. -/
abbrev ExecutionFrame := SailFrame (fun reg => SailSnapshot.executionRegister reg = false)

end SP1Clean.Semantics
