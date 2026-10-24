module

public import SP1CleanTest.Core.ComponentExport
public import SP1Clean.Proofs.Chips.AddChip.Formal
public import SP1Clean.Proofs.Chips.AddiChip.Formal
public import SP1Clean.Proofs.Chips.AddwChip.Formal
public import SP1Clean.Proofs.Chips.SubChip.Formal
public import SP1Clean.Proofs.Chips.SubwChip.Formal
public import SP1Clean.Proofs.Chips.BitwiseChip.Formal
public import SP1Clean.Proofs.Chips.LtChip.Formal
public import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
public import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
public import SP1Clean.Proofs.Chips.JalChip.Formal
public import SP1Clean.Proofs.Chips.JalrChip.Formal
public import SP1Clean.Proofs.Chips.BranchChip.Formal
public import SP1Clean.Proofs.Chips.UTypeChip.Formal
public import SP1Clean.Proofs.Chips.LoadByteChip.Formal
public import SP1Clean.Proofs.Chips.LoadHalfChip.Formal
public import SP1Clean.Proofs.Chips.LoadWordChip.Formal
public import SP1Clean.Proofs.Chips.LoadDoubleChip.Formal
public import SP1Clean.Proofs.Chips.LoadX0Chip.Formal
public import SP1Clean.Proofs.Chips.StoreByteChip.Formal
public import SP1Clean.Proofs.Chips.StoreHalfChip.Formal
public import SP1Clean.Proofs.Chips.StoreWordChip.Formal
public import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
public import SP1Clean.Proofs.Chips.MulChip.Formal
public import SP1Clean.Proofs.Chips.DivRemChip.Complete
public import SP1Clean.Proofs.Chips.AluX0Chip.Formal

/-! # Instruction-local Rust export

Export production instruction components through Clean's built-in lowering and Rust emitter.
Each surrounding singleton has no providers: its channels remain open, so it is a row-level
comparison fixture, not an executable SP1 ensemble or a proof of global balance.
-/

@[expose] public section

namespace SP1CleanTest.Core.InstructionExport

open Air.Flat SP1Clean

open ComponentExport

/-- All supported instruction families in release order. DivRem alone selects DIVU on padding;
the other components generate their padding witnesses from zero inputs. -/
def rustExports : List (String × Except String String) := [
  ("add_instruction.rs", exportRust AddChip.circuit),
  ("addi_instruction.rs", exportRust AddiChip.circuit),
  ("addw_instruction.rs", exportRust AddwChip.circuit),
  ("sub_instruction.rs", exportRust SubChip.circuit),
  ("subw_instruction.rs", exportRust SubwChip.circuit),
  ("bitwise_instruction.rs", exportRust BitwiseChip.circuit),
  ("lt_instruction.rs", exportRust LtChip.circuit),
  ("shift_left_instruction.rs", exportRust ShiftLeftChip.circuit),
  ("shift_right_instruction.rs", exportRust ShiftRightChip.circuit),
  ("jal_instruction.rs", exportRust JalChip.circuit),
  ("jalr_instruction.rs", exportRust JalrChip.circuit),
  ("branch_instruction.rs", exportRust BranchChip.circuit),
  ("u_type_instruction.rs", exportRust UTypeChip.circuit),
  ("load_byte_instruction.rs", exportRust LoadByteChip.circuit),
  ("load_half_instruction.rs", exportRust LoadHalfChip.circuit),
  ("load_word_instruction.rs", exportRust LoadWordChip.circuit),
  ("load_double_instruction.rs", exportRust LoadDoubleChip.circuit),
  ("load_x0_instruction.rs", exportRust LoadX0Chip.circuit),
  ("store_byte_instruction.rs", exportRust StoreByteChip.circuit),
  ("store_half_instruction.rs", exportRust StoreHalfChip.circuit),
  ("store_word_instruction.rs", exportRust StoreWordChip.circuit),
  ("store_double_instruction.rs", exportRust StoreDoubleChip.circuit),
  ("mul_instruction.rs", exportRust MulChip.circuit),
  ("div_rem_instruction.rs", exportRust DivRemChip.circuit
    (toElements (TraceGen.divRemPaddingInputs (p := SP1Prime))).toArray),
  ("alu_x0_instruction.rs", exportRust AluX0Chip.circuit)]

end SP1CleanTest.Core.InstructionExport
