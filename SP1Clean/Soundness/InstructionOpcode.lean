import SP1Clean.Soundness.WitnessDecode

/-! # Opcode membership of a grounded ordinary instruction
The selected flags and authenticated circuit columns place every active opcode in the existing
instruction family's route. This also distinguishes the two jump-link producers on the shared
Program ledger.
-/

namespace SP1Clean.Soundness

open Semantics Target LeanRV64D

variable {p : ℕ} [Fact p.Prime]

private theorem opcode_mem {id : InstructionChipId} {opcode : ZMod p} {value : ℕ}
    (same : opcode = (value : ZMod p)) (listed : value ∈ id.route.opcodes.map Opcode.toNat) :
    opcode ∈ id.route.opcodes.map (fun o => (o.toNat : ZMod p)) := by
  obtain ⟨o, member, rfl⟩ := List.mem_map.mp listed
  exact List.mem_map.mpr ⟨o, member, same.symm⟩

variable [Fact (2 ^ 24 < p)]

/-- A real, grounded native row emits an opcode belonging to its physical instruction family. -/
theorem supportedChipFor_opcode_mem (id : InstructionChipId) :
    ∀ (input : (supportedChipFor (p := p) id).kind.Inputs (ZMod p))
      (cols : (supportedChipFor (p := p) id).kind.Cols (ZMod p))
      (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState),
      ((supportedChipFor id).kind.view input cols).is_real = 1 →
      (supportedChipFor id).kind.chipSpec input cols data →
      (supportedChipFor id).kind.advanceReady input cols program source →
      (programAccess ((supportedChipFor id).kind.view input cols)).toRow.opcode ∈
        id.route.opcodes.map (fun o => (o.toNat : ZMod p)) := by
  cases id <;> intro input cols data program source real spec ready
  case add =>
    exact opcode_mem (value := 0) (by change (0 : ZMod p) = (0 : ℕ); norm_num) (by decide)
  case addi =>
    exact opcode_mem (value := 1) (by change (1 : ZMod p) = (1 : ℕ); norm_num) (by decide)
  case addw =>
    exact opcode_mem (value := 19) rfl (by decide)
  case sub =>
    exact opcode_mem (value := 2) rfl (by decide)
  case subw =>
    exact opcode_mem (value := 20) rfl (by decide)
  case jal =>
    exact opcode_mem (value := 46) rfl (by decide)
  case jalr =>
    exact opcode_mem (value := 47) rfl (by decide)
  case loadDouble =>
    exact opcode_mem (value := 35) rfl (by decide)
  case storeByte => exact opcode_mem (value := 36) rfl (by decide)
  case storeHalf => exact opcode_mem (value := 37) rfl (by decide)
  case storeWord => exact opcode_mem (value := 38) rfl (by decide)
  case storeDouble => exact opcode_mem (value := 39) rfl (by decide)
  case bitwise =>
    change (programAccess (BitwiseChip.rowView input cols)).toRow.opcode ∈ _
    have flags := ready.2.2.2.1
    rcases flags with active | active | active
    · have others := spec.2.2.2.2.2.1 active
      exact opcode_mem (value := 5) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide)
    · have others := spec.2.2.2.2.2.2.1 active
      exact opcode_mem (value := 4) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide)
    · have others := spec.2.2.2.2.2.2.2 active
      exact opcode_mem (value := 3) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide)
  case lt =>
    change (programAccess (LtChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact opcode_mem (value := 9) (by simp [programAccess, ProgramAccess.toRow, LtChip.rowView, a, b]) (by decide)
    · exact opcode_mem (value := 10) (by simp [programAccess, ProgramAccess.toRow, LtChip.rowView, a, b]) (by decide)
  case shiftLeft =>
    change (programAccess (ShiftLeftChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2.2.2.2.2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact opcode_mem (value := 6) (by simp [programAccess, ProgramAccess.toRow, ShiftLeftChip.rowView, a, b]) (by decide)
    · exact opcode_mem (value := 21) (by simp [programAccess, ProgramAccess.toRow, ShiftLeftChip.rowView, a, b]) (by decide)
  case loadByte =>
    change (programAccess (LoadByteChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact opcode_mem (value := 29) (by simp [programAccess, ProgramAccess.toRow, LoadByteChip.rowView, a, b]) (by decide)
    · exact opcode_mem (value := 32) (by simp [programAccess, ProgramAccess.toRow, LoadByteChip.rowView, a, b]) (by decide)
  case loadHalf =>
    change (programAccess (LoadHalfChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact opcode_mem (value := 30) (by simp [programAccess, ProgramAccess.toRow, LoadHalfChip.rowView, a, b]) (by decide)
    · exact opcode_mem (value := 33) (by simp [programAccess, ProgramAccess.toRow, LoadHalfChip.rowView, a, b]) (by decide)
  case loadWord =>
    change (programAccess (LoadWordChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact opcode_mem (value := 31) (by simp [programAccess, ProgramAccess.toRow, LoadWordChip.rowView, a, b]) (by decide)
    · exact opcode_mem (value := 34) (by simp [programAccess, ProgramAccess.toRow, LoadWordChip.rowView, a, b]) (by decide)
  case shiftRight =>
    change (programAccess (ShiftRightChip.rowView input cols)).toRow.opcode ∈ _
    have flags := ready.2.2.2.2.2
    rcases flags with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact opcode_mem (value := 7) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide)
    · exact opcode_mem (value := 8) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide)
    · exact opcode_mem (value := 22) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide)
    · exact opcode_mem (value := 23) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide)
  case mul =>
    change (programAccess (MulChip.rowView input cols)).toRow.opcode ∈ _
    have flags := ready.2.2
    simp only [MulChip.SelectorOneHot, MulChip.selectors] at flags
    rcases flags with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩
    · exact opcode_mem (value := 11) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide)
    · exact opcode_mem (value := 12) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide)
    · exact opcode_mem (value := 13) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide)
    · exact opcode_mem (value := 14) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide)
    · exact opcode_mem (value := 24) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide)
  case branch =>
    change (programAccess (BranchChip.rowView input cols)).toRow.opcode ∈ _
    have flags := spec.2.2.2.1 real
    simp only [BranchChip.flagsOneHot] at flags
    rcases flags with ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩
    · exact opcode_mem (value := 40) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
    · exact opcode_mem (value := 41) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
    · exact opcode_mem (value := 42) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
    · exact opcode_mem (value := 43) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
    · exact opcode_mem (value := 44) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
    · exact opcode_mem (value := 45) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide)
  case uType =>
    change (programAccess (UTypeChip.rowView input cols)).toRow.opcode ∈ _
    rcases ready.2 with flag | flag
    · exact opcode_mem (value := 49) (by simp [programAccess, ProgramAccess.toRow, UTypeChip.rowView, flag]) (by decide)
    · exact opcode_mem (value := 48) (by simp [programAccess, ProgramAccess.toRow, UTypeChip.rowView, flag]) (by decide)
  case divRem =>
    obtain ⟨selected, selection⟩ := spec.2.selection real
    exact opcode_mem selection.encodedOpcode
      (by cases selected <;> decide)
  case aluX0 =>
    have listed : ∀ k ∈ List.range 29, k ∈ InstructionChipId.aluX0.route.opcodes.map Opcode.toNat := by decide
    exact opcode_mem (ZMod.natCast_zmod_val _).symm (listed _ (List.mem_range.mpr ready.2.2))
  case loadX0 =>
    rcases ready.2.2 with ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩ |
      ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩
    · exact opcode_mem (value := 29) opcode (by decide)
    · exact opcode_mem (value := 32) opcode (by decide)
    · exact opcode_mem (value := 30) opcode (by decide)
    · exact opcode_mem (value := 33) opcode (by decide)
    · exact opcode_mem (value := 31) opcode (by decide)
    · exact opcode_mem (value := 34) opcode (by decide)
    · exact opcode_mem (value := 35) opcode (by decide)

end SP1Clean.Soundness
