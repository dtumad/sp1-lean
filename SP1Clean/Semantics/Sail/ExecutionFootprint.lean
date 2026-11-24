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

/-- The five-bit architectural index carried by a generated Sail `regidx`. -/
def regidxBits : regidx → BitVec 5
  | .Regidx bits => bits

/-- The architectural destination, if any, of an ordinary instruction in the supported fragment.
The A read-back of a store or branch is a source operand. -/
def instructionDestination? : instruction → Option (BitVec 5)
  | .RTYPE (_, _, rd, _) | .RTYPEW (_, _, rd, _)
  | .MUL (_, _, rd, _) | .MULW (_, _, rd)
  | .DIV (_, _, rd, _) | .DIVW (_, _, rd, _)
  | .REM (_, _, rd, _) | .REMW (_, _, rd, _)
  | .ITYPE (_, _, rd, _) | .SHIFTIOP (_, _, rd, _)
  | .SHIFTIWOP (_, _, rd, _) | .ADDIW (_, _, rd)
  | .UTYPE (_, rd, _) | .JAL (_, rd) | .JALR (_, _, rd)
  | .LOAD (_, _, rd, _, _) => some (regidxBits rd)
  | _ => none

/-- The execute-stage register frame specialized to its one decoded destination. -/
abbrev DestinationFrame (destination : Option (BitVec 5)) := SailFrame (fun reg => reg ≠ .nextPC ∧
  ∀ index : BitVec 5, destination = some index → index ≠ 0 → reg ≠ reg_idx_to_Register index)

/-- Forgetting which GPR was selected preserves the general platform and simulator frame. -/
theorem DestinationFrame.executeFrame {destination : Option (BitVec 5)} {source target : SailState}
    (frame : DestinationFrame destination source target) : ExecuteFrame source target :=
  ⟨fun reg fixed => frame.registers reg ⟨fixed.1, fun index _ => fixed.2 index⟩, frame.cycles, frame.output⟩

/-- A stage with no GPR destination satisfies every less precise destination frame. -/
theorem DestinationFrame.of_none {source target : SailState} (frame : DestinationFrame none source target)
    (destination : Option (BitVec 5)) : DestinationFrame destination source target :=
  ⟨fun reg fixed => frame.registers reg ⟨fixed.1, fun _ h => nomatch h⟩, frame.cycles, frame.output⟩

/-- The complete transition also includes the official prelude and retirement writes. -/
abbrev ExecutionFrame := SailFrame (fun reg => SailSnapshot.executionRegister reg = false)

end SP1Clean.Semantics
