import SP1Clean.Soundness.InstructionOpcode
import SP1Clean.Soundness.StoreWritePolicy

/-! # Write permission for the supported instruction registry

Committed decoding rules out stores for every non-store opcode. The four store families identify
their exact decoded byte intervals with the intervals authorized by the native permission ledger.
The result concerns incoming Sail operands, including stores that leave memory unchanged.
-/

namespace SP1Clean.Soundness

open Semantics Target LeanRV64D

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Committed non-store opcodes require no memory-write permission. -/
theorem Target.decodedInROM.permittedAt_of_nonstore {program : GuestProgram}
    {row : ProgramChip.ProgramRow (ZMod p)} (decoded : decodedInROM program row)
    {source : SailState} (pc : source.regs.get? Register.PC = some (pcBitsOfRow row))
    (readOnly : ℕ → Bool)
    (nonstore : ∀ width, row.opcode ≠ ((storeOpcode width).toNat : ZMod p)) :
    InstructionWrite.PermittedAt readOnly program source := by
  obtain ⟨word, instruction, fetched, decode, projected⟩ := decoded
  obtain ⟨_, chip, _, routed⟩ := instrToProgramRow'_route_exists projected
  refine ⟨_, word, instruction, pc, fetched, decode,
    InstructionWrite.check_of_nonstore _ _ _ (instructionImageOK_of_instrToProgramRow'_some projected)
      (by simp only [routed, Option.isSome_some]) ?_⟩
  intro offset rs2 rs1 width equal
  subst instruction
  have projected' := instrToProgramRow'_some projected
  have opcode := congrArg (fun value => value.map ProgramChip.ProgramRow.opcode) projected'
  simp only [instrToProgramRow, Option.map_some, Option.some.injEq] at opcode
  exact nonstore width opcode.symm

variable [Fact (2 ^ 24 < p)]

/-- Every registered chip authorizes the decoded instruction's complete write footprint from
its proved row contract, grounded readiness, and native byte-permission ledger. -/
theorem supportedChipFor_write_permittedAt (id : InstructionChipId) :
    ∀ (input : (supportedChipFor (p := p) id).kind.Inputs (ZMod p))
      (cols : (supportedChipFor (p := p) id).kind.Cols (ZMod p))
      (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState),
      ((supportedChipFor id).kind.view input cols).is_real = 1 →
      (supportedChipFor id).kind.chipSpec input cols data →
      (supportedChipFor id).kind.advanceReady input cols program source →
      source.regs.get? Register.PC =
        some (pcBitsOfRow (programAccess ((supportedChipFor id).kind.view input cols)).toRow) →
      ValueOperandsBound ((supportedChipFor id).kind.view input cols) source →
      decodedInROM program (programAccess ((supportedChipFor id).kind.view input cols)).toRow →
      ∀ image : ProgramImage, RowWritePermitted image ((supportedChipFor id).kind.view input cols) →
        InstructionWrite.PermittedAt image.readOnly program source := by
  intro input cols data program source real spec ready pc operands decoded image permitted
  by_cases store : id = .storeByte ∨ id = .storeHalf ∨ id = .storeWord ∨ id = .storeDouble
  · rcases store with rfl | rfl | rfl | rfl
    · exact StoreByteChip.write_permittedAt input cols data program source real spec
        ready.2.1 ready.2.2.1 pc operands decoded permitted
    · exact StoreHalfChip.write_permittedAt input cols data program source real spec
        ready.2.1 ready.2.2.1 pc operands decoded permitted
    · exact StoreWordChip.write_permittedAt input cols data program source real spec
        ready.2.1 ready.2.2.1 pc operands decoded permitted
    · exact StoreDoubleChip.write_permittedAt input cols data program source real spec
        ready.2.1 ready.2.2.1 pc operands decoded permitted
  apply decoded.permittedAt_of_nonstore pc image.readOnly
  intro width equal
  obtain ⟨opcode, member, same⟩ := List.mem_map.mp
    (supportedChipFor_opcode_mem id input cols data program source real spec ready)
  have code := opcodeCast_inj (same.trans equal)
  have excludes : ∀ i : InstructionChipId,
      ¬(i = .storeByte ∨ i = .storeHalf ∨ i = .storeWord ∨ i = .storeDouble) →
      ∀ op ∈ i.route.opcodes, op.toNat ∉ [36, 37, 38, 39] := by
    intro i
    cases i <;> decide
  apply excludes id store opcode member
  rw [code]
  unfold storeOpcode
  split_ifs <;> decide

/-- The registry result at an actual decoded physical row. Static soundness and grounded
readiness are supplied by the existing chip contracts, without a new permission assumption. -/
theorem DecodedInstructionRow.write_permittedAt (row : DecodedInstructionRow p)
    (registered : row.chip ∈ supportedChips (p := p)) (data : ProverData (ZMod p))
    (program : GuestProgram) (source : SailState)
    (real : (row.toChipRow data).is_real = 1)
    (spec : (row.toChipRow data).chipSpec data)
    (ready : (row.toChipRow data).kind.advanceReady
      (row.toChipRow data).inputs (row.toChipRow data).cols program source)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (row.toChipRow data).view).toRow))
    (operands : ValueOperandsBound (row.toChipRow data).view source)
    (decoded : decodedInROM program (programAccess (row.toChipRow data).view).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (row.toChipRow data).view) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  obtain ⟨chip, physical⟩ := row
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp registered
  exact supportedChipFor_write_permittedAt id _ _ data program source real spec ready
    pc operands decoded image permitted

end SP1Clean.Soundness
