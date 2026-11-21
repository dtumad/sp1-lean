import SP1Clean.Soundness.Grounding.ControlFlowChips
import SP1Clean.Soundness.Grounding.JTypeChips
import SP1Clean.Soundness.InstructionOpcode
import SP1Clean.Soundness.RowSoundness
import SP1Clean.Proofs.Chips.JumpLinkBound
import SP1Clean.Semantics.Execution.ReleaseLinks

/-! # Released jump links at authenticated ordinary instruction rows

Committed Program decoding selects the instruction and destination register. The native jump
constraint supplies the enabled link bound at the same physical row.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat Semantics Target LeanRV64D

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem regidxVal_ne_zero {rd : BitVec 5} (nonzero : rd ≠ 0) :
    regidxVal (p := p) (.Regidx rd) ≠ 0 := by
  intro zero
  apply nonzero
  apply regidx_bv_inj (p := p)
  simpa [regidxVal] using zero

private theorem decoded_releaseLinkAt {program : GuestProgram} {source : SailState}
    {row : ProgramChip.ProgramRow (ZMod p)} (decoded : decodedInROM program row)
    (cfg : SailConfigured source) (atPc : source.regs.get? Register.PC = some (pcBitsOfRow row))
    (bounded : (row.opcode = (Opcode.JAL.toNat : ZMod p) ∨ row.opcode = (Opcode.JALR.toNat : ZMod p)) →
      row.op_a_0 = 0 → (pcBitsOfRow row).toNat + 4 < 2 ^ 48) : ReleaseLinkAt program source := by
  obtain ⟨word, instr, fetch, official, projection⟩ := decoded.decodes source cfg
  apply (releaseLinkAt_iff atPc fetch official).mpr
  unfold instructionLinkFits
  split
  next imm rd =>
    intro nonzero
    have same := Option.some.inj projection
    apply bounded (Or.inl (congrArg ProgramChip.ProgramRow.opcode same.symm))
    rw [← same]
    exact ite_eq_right (regidxVal_ne_zero nonzero)
  next imm rs1 rd =>
    intro nonzero
    have same := Option.some.inj projection
    apply bounded (Or.inr (congrArg ProgramChip.ProgramRow.opcode same.symm))
    rw [← same]
    exact ite_eq_right (regidxVal_ne_zero nonzero)
  next => trivial

omit [Fact (2 ^ 17 < p)] in
private theorem pcBits_le (pc : Vector (ZMod p) 3) :
    (pcBitsOfVals pc[0].val pc[1].val pc[2].val).toNat ≤ (JumpLink.pcWord pc).toNat := by
  let value := pc[0].val + pc[1].val * 2 ^ 16 + pc[2].val * 2 ^ 32
  have word : (JumpLink.pcWord pc).toNat = value := by
    change value + (0 : ZMod p).val * 2 ^ 48 = value
    rw [ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
  rw [word, pcBitsOfVals, BitVec.toNat_ofNat]
  exact Nat.mod_le value (2 ^ 64)

variable [Fact (2 ^ 24 < p)]

private theorem jal_bound (env : Environment (ZMod p))
    (assumes : (supportedChipFor (p := p) .jal).table.CircuitAssumptions env)
    (checked : (supportedChipFor (p := p) .jal).table.operations.ConstraintsHold env)
    (funded : (supportedChipFor (p := p) .jal).table.operations.FullGuarantees env)
    (real : ((supportedChipFor (p := p) .jal).table.rowInput env).is_real = 1)
    (write : ((supportedChipFor (p := p) .jal).table.rowOutput env).adapter.op_a_0 = 0) :
    let pc := ((supportedChipFor (p := p) .jal).table.rowOutput env).state.pc
    (pcBitsOfVals pc[0].val pc[1].val pc[2].val).toNat + 4 < 2 ^ 48 := by
  let component : Component (ZMod p) := { (supportedChipFor (p := p) .jal).table with
    circuit := { JalChip.circuit with Spec := _, soundness := JumpLink.jal } }
  have bound := (Component.weakSoundness (component := component) assumes checked funded).1
  change JumpLinkFits (JumpLink.pcWord _).toNat (_ - _ = 1) at bound
  have inputEq := eval_varFromOffset_valueFromOffset JalChip.Inputs 0 env
  change (jalViewOf env).adapter.op_a_0 = 0 at write
  rw [jalViewOf_adapter, inputEq] at write
  have enabled : ((supportedChipFor (p := p) .jal).table.rowInput env).is_real -
      ((supportedChipFor (p := p) .jal).table.rowInput env).adapter.op_a_0 = 1 := by
    rw [real, show ((supportedChipFor (p := p) .jal).table.rowInput env).adapter.op_a_0 = 0 from write, sub_zero]
  change (pcBitsOfVals (jalViewOf env).state.pc[0].val (jalViewOf env).state.pc[1].val
    (jalViewOf env).state.pc[2].val).toNat + 4 < 2 ^ 48
  rw [jalViewOf_state, inputEq]
  exact lt_of_le_of_lt (Nat.add_le_add_right (pcBits_le _) _) (bound enabled)

private theorem jalr_bound (env : Environment (ZMod p))
    (assumes : (supportedChipFor (p := p) .jalr).table.CircuitAssumptions env)
    (checked : (supportedChipFor (p := p) .jalr).table.operations.ConstraintsHold env)
    (funded : (supportedChipFor (p := p) .jalr).table.operations.FullGuarantees env)
    (real : ((supportedChipFor (p := p) .jalr).table.rowInput env).is_real = 1)
    (write : ((supportedChipFor (p := p) .jalr).table.rowOutput env).adapter.op_a_0 = 0) :
    let pc := ((supportedChipFor (p := p) .jalr).table.rowOutput env).state.pc
    (pcBitsOfVals pc[0].val pc[1].val pc[2].val).toNat + 4 < 2 ^ 48 := by
  let component : Component (ZMod p) := { (supportedChipFor (p := p) .jalr).table with
    circuit := { JalrChip.circuit with Spec := _, soundness := JumpLink.jalr } }
  have bound := (Component.weakSoundness (component := component) assumes checked funded).1
  change JumpLinkFits (JumpLink.pcWord _).toNat (_ - _ = 1) at bound
  have inputEq := eval_varFromOffset_valueFromOffset JalrChip.Inputs 0 env
  change (jalrViewOf env).adapter.op_a_0 = 0 at write
  rw [jalrViewOf_adapter, inputEq] at write
  have enabled : ((supportedChipFor (p := p) .jalr).table.rowInput env).is_real -
      ((supportedChipFor (p := p) .jalr).table.rowInput env).adapter.op_a_0 = 1 := by
    rw [real, show ((supportedChipFor (p := p) .jalr).table.rowInput env).adapter.op_a_0 = 0 from write, sub_zero]
  change (pcBitsOfVals (jalrViewOf env).state.pc[0].val (jalrViewOf env).state.pc[1].val
    (jalrViewOf env).state.pc[2].val).toNat + 4 < 2 ^ 48
  rw [jalrViewOf_state, inputEq]
  exact lt_of_le_of_lt (Nat.add_le_add_right (pcBits_le _) _) (bound enabled)

/-- A registered ordinary row authenticates the released enabled-link check against its actual
Sail source. The Program channel identifies the decoded instruction and its destination register. -/
theorem DecodedInstructionRow.releaseLinkAt (row : DecodedInstructionRow p)
    {data : ProverData (ZMod p)} {program : GuestProgram} {source : SailState}
    (fixed : DecodedRowStaticInputs row data) (dynamic : DecodedRowDynamicInputs row data program source)
    (real : (row.toChipRow data).is_real = 1)
    (decoded : decodedInROM program (programAccess (row.toChipRow data).view).toRow)
    (atPc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (row.toChipRow data).view).toRow))
    (configured : SailConfigured source) : ReleaseLinkAt program source := by
  apply decoded_releaseLinkAt decoded configured atPc
  intro jump write
  have funded := (DecodedRowChannelGuarantees.mk (decodedRow_stateChannelGuarantees row data)
    fixed.byte fixed.program dynamic.circuit.memory).full fixed.channels
  have spec := fixed.chipSpec dynamic.circuit
  obtain ⟨chip, physical⟩ := row
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp fixed.registered
  obtain ⟨op, present, same⟩ := List.mem_map.mp
    (supportedChipFor_opcode_mem id _ _ data program source real spec dynamic.ready)
  rcases jump with jal | jalr
  · have found : ∀ i : InstructionChipId, ∀ o ∈ i.route.opcodes, o.toNat = Opcode.JAL.toNat → i = .jal := by
      intro i
      cases i <;> decide
    obtain rfl := found id op present (opcodeCast_inj (same.trans jal))
    exact jal_bound _ dynamic.circuit.assumptions fixed.constraints funded real write
  · have found : ∀ i : InstructionChipId, ∀ o ∈ i.route.opcodes, o.toNat = Opcode.JALR.toNat → i = .jalr := by
      intro i
      cases i <;> decide
    obtain rfl := found id op present (opcodeCast_inj (same.trans jalr))
    exact jalr_bound _ dynamic.circuit.assumptions fixed.constraints funded real write

end SP1Clean.Soundness
