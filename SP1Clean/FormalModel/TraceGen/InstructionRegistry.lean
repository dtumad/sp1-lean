module

public import SP1Clean.Model.InstructionChipId
public import SP1Clean.FormalModel.TraceGen.Events

/-! # Semantic events indexed by the native instruction registry

Each instruction identity selects its field-free event type and semantic validity predicate.
The chronological compiler and physical table assembly share these families. They do not depend
on table construction, witness capacity or extracted Rust columns.
-/

@[expose] public section

namespace SP1Clean.InstructionChipId

open SP1Clean.TraceGen

/-- Semantic event type routed to one instruction table. -/
def Event : InstructionChipId → Type
  | .add => RTypeEvent
  | .addi => ITypeEvent
  | .addw => ALUTypeEvent
  | .sub => RTypeEvent
  | .subw => RTypeEvent
  | .bitwise => ALUTypeEvent
  | .lt => ALUTypeEvent
  | .shiftLeft => ALUTypeEvent
  | .shiftRight => ALUTypeEvent
  | .jal => JTypeEvent
  | .jalr => ITypeEvent
  | .branch => ITypeEvent
  | .uType => JTypeEvent
  | .loadByte => MemoryEvent
  | .loadHalf => MemoryEvent
  | .loadWord => MemoryEvent
  | .loadDouble => MemoryEvent
  | .loadX0 => MemoryEvent
  | .storeByte => MemoryEvent
  | .storeHalf => MemoryEvent
  | .storeWord => MemoryEvent
  | .storeDouble => MemoryEvent
  | .mul => RTypeEvent
  | .divRem => RTypeEvent
  | .aluX0 => ALUTypeEvent

/-- Routing and semantic side condition required by one instruction table's trace builder. -/
def Valid : (id : InstructionChipId) → id.Event → Prop
  | .add, e => e.WellFormed
  | .addi, e => e.WellFormed
  | .addw, e => e.WellFormed
  | .sub, e => e.WellFormed
  | .subw, e => e.WellFormed
  | .bitwise, e => e.WellFormed ∧ e.IsBitwise
  | .lt, e => e.WellFormed ∧ e.IsLt
  | .shiftLeft, e => e.WellFormed ∧ e.IsShiftLeft
  | .shiftRight, e => e.WellFormed ∧ e.IsShiftRight
  | .jal, e => e.WellFormedJal ∧ e.JalTargets
  | .jalr, e => e.WellFormedJalr ∧ e.JalrTargets
  | .branch, e => e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets
  | .uType, e => e.WellFormedUType ∧ e.UTypeImm
  | .loadByte, e => e.WellFormed ∧ (e.opcode = 29 ∨ e.opcode = 32)
  | .loadHalf, e => e.WellFormed ∧ e.Aligned 2
  | .loadWord, e => e.WellFormed ∧ e.Aligned 4
  | .loadDouble, e => e.WellFormed ∧ e.Aligned 8
  | .loadX0, e => e.WellFormedX0 ∧ e.IsLoad
  | .storeByte, e => e.WellFormedStore
  | .storeHalf, e => e.WellFormedStore ∧ e.Aligned 2
  | .storeWord, e => e.WellFormedStore ∧ e.Aligned 4
  | .storeDouble, e => e.WellFormedStore ∧ e.Aligned 8
  | .mul, e => e.WellFormed ∧ e.IsMul
  | .divRem, e => e.WellFormed ∧ e.IsDivRem
  | .aluX0, e => e.WellFormedX0

end SP1Clean.InstructionChipId
