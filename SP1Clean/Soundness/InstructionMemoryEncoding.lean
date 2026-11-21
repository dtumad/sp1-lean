import SP1Clean.Soundness.InstructionOpcode
import SP1Clean.Soundness.RowSoundness
import SP1Clean.Semantics.Execution.ExecutionEncoding

/-! # Memory encoding of a grounded physical instruction

The Program row identifies the architectural base and offset. The load reader's grounded
address bounds and the store address operation supply width alignment and the complete guest
span for the wrapped RV64 address.
-/

namespace SP1Clean.Soundness

open Circuit Semantics Target LeanRV64D

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private def Access (view : Trace.RowView (ZMod p)) (width : ℕ) : Prop :=
  let address := (Word.toBitVec64 view.adapter.op_b_memory.prev_value + Word.toBitVec64 view.adapter.op_c).toNat
  NativeLayout.guestMemory.ContainsSpan address width ∧ address % width = 0

private theorem operandSpan {view : Trace.RowView (ZMod p)} {source : SailState}
    (operands : ValueOperandsBound view source) (baseReg : view.adapter.imm_b = 0)
    (rs1 : regidx) (offset : BitVec 12) (width : word_width)
    (baseIndex : view.adapter.op_b = #v[regidxVal rs1, 0, 0, 0])
    (offsetWord : view.adapter.op_c = bitVecToWord (offset.signExtend 64))
    (access : Access view width.toNat) :
    ∃ base, source.get_reg? (regidxBits rs1) = some base ∧
      NativeLayout.guestMemory.ContainsSpan (memoryEffectiveAddress base offset).toNat width.toNat ∧
      (memoryEffectiveAddress base offset).toNat % width.toNat = 0 := by
  obtain ⟨rs1⟩ := rs1
  refine ⟨_, operands.1 rs1 baseReg (by rw [baseIndex]; rfl), ?_⟩
  unfold Access at access
  rw [offsetWord, toBitVec64_bitVecToWord] at access
  exact access

private theorem encodedLoad {view : Trace.RowView (ZMod p)} {source : SailState}
    {instr : instruction} {pc : Vector (ZMod p) 3} (width : word_width) (unsigned : Bool)
    (allowed : loadWidthOK width unsigned = true)
    (projection : instrToProgramRow' pc instr = some (programAccess view).toRow)
    (opcode : (programAccess view).toRow.opcode = ((loadOpcode width unsigned).toNat : ZMod p))
    (operands : ValueOperandsBound view source) (baseReg : view.adapter.imm_b = 0)
    (immediate : (programAccess view).toRow.imm_c = 1) (access : Access view width.toNat) :
    instructionMemoryEncoded source.get_reg? instr := by
  obtain ⟨offset, rs1, _, rfl, _, index, word⟩ :=
    instrToProgramRow_inv_load' width unsigned allowed projection opcode immediate
  exact operandSpan operands baseReg rs1 offset width index word access

private theorem encodedStore {view : Trace.RowView (ZMod p)} {source : SailState}
    {instr : instruction} {pc : Vector (ZMod p) 3} (width : word_width)
    (allowed : storeWidthOK width = true)
    (projection : instrToProgramRow' pc instr = some (programAccess view).toRow)
    (opcode : (programAccess view).toRow.opcode = ((storeOpcode width).toNat : ZMod p))
    (operands : ValueOperandsBound view source) (baseReg : view.adapter.imm_b = 0)
    (immediate : (programAccess view).toRow.imm_c = 1) (access : Access view width.toNat) :
    instructionMemoryEncoded source.get_reg? instr := by
  obtain ⟨offset, _, rs1, rfl, _, index, word⟩ :=
    instrToProgramRow_inv_store' width allowed projection opcode immediate
  exact operandSpan operands baseReg rs1 offset width index word access

omit [Fact (2 ^ 17 < p)] in
private theorem storeSpan (width : ℕ) (supported : width ∈ [1, 2, 4, 8])
    (input : AddressOperation.Inputs (ZMod p))
    (base : Word.isU64 input.b) (offset : Word.isU64 input.cc)
    (valid : AddressOperation.ValidAddress input)
    (aligned : (input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val) % width = 0) :
    let address := (AddressOperation.effectiveAddress input).toNat
    NativeLayout.guestMemory.ContainsSpan address width ∧ address % width = 0 := by
  obtain ⟨upper, lower, bits⟩ := AddressOperation.effectiveAddress_facts base offset valid
  rw [bits] at aligned
  have divisor : width ∣ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl <;> decide
  rw [Nat.mod_mod_of_dvd _ divisor] at aligned
  refine ⟨⟨lower, ?_⟩, aligned⟩
  change _ + width ≤ 2 ^ 48
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl <;> omega

private theorem nonmemory {pc : Vector (ZMod p) 3} {instr : instruction} {row : ProgramChip.ProgramRow (ZMod p)}
    (projected : instrToProgramRow' pc instr = some row)
    (outside : row.opcode.val < 29 ∨ 39 < row.opcode.val) (register : BitVec 5 → Option (BitVec 64)) :
    instructionMemoryEncoded register instr := by
  unfold instructionMemoryEncoded
  split <;> try trivial
  all_goals
    have plain := instrToProgramRow'_some projected
    have op := congrArg (fun item => item.map ProgramChip.ProgramRow.opcode) plain
    simp only [instrToProgramRow, Option.map_some, Option.some.injEq] at op
    rw [← op, ZMod.val_natCast_of_lt (lt_trans (opcode_toNat_lt _) (by have := Fact.out (p := 2 ^ 17 < p); omega))] at outside
    first | unfold loadOpcode at outside | unfold storeOpcode at outside
    split_ifs at outside <;> simp [Opcode.toNat] at outside

variable [Fact (2 ^ 24 < p)]

/-- The installed ordinary instruction's semantic access stays aligned and within guest RAM. -/
theorem supportedChipFor_memoryEncoded (id : InstructionChipId)
    (input : (supportedChipFor (p := p) id).kind.Inputs (ZMod p))
    (cols : (supportedChipFor (p := p) id).kind.Cols (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState)
    (real : ((supportedChipFor id).kind.view input cols).is_real = 1)
    (spec : (supportedChipFor id).kind.chipSpec input cols data)
    (ready : (supportedChipFor id).kind.advanceReady input cols program source)
    (operands : ValueOperandsBound ((supportedChipFor id).kind.view input cols) source)
    {pc : Vector (ZMod p) 3} {instr : instruction}
    (projection : instrToProgramRow' pc instr = some (programAccess ((supportedChipFor id).kind.view input cols)).toRow) :
    instructionMemoryEncoded source.get_reg? instr := by
  have routed := supportedChipFor_opcode_mem id input cols data program source real spec ready
  by_cases memory : id ∈ [.loadByte, .loadHalf, .loadWord, .loadDouble, .loadX0, .storeByte, .storeHalf, .storeWord, .storeDouble]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at memory
    rcases memory with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, hi, lo, _⟩ := ready
      rcases List.mem_cons.mp routed with op | rest
      · exact encodedLoad 1 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, Nat.mod_one _⟩
      · exact encodedLoad 1 true (by decide) projection (List.mem_singleton.mp rest) operands rfl rfl ⟨⟨lo, hi⟩, Nat.mod_one _⟩
    · obtain ⟨_, _, _, _, al, hi, lo, _⟩ := ready
      rcases List.mem_cons.mp routed with op | rest
      · exact encodedLoad 2 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 2 true (by decide) projection (List.mem_singleton.mp rest) operands rfl rfl ⟨⟨lo, hi⟩, al⟩
    · obtain ⟨_, _, _, _, _, al, hi, lo, _⟩ := ready
      rcases List.mem_cons.mp routed with op | rest
      · exact encodedLoad 4 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 4 true (by decide) projection (List.mem_singleton.mp rest) operands rfl rfl ⟨⟨lo, hi⟩, al⟩
    · obtain ⟨_, _, _, _, _, _, al, hi, lo, _⟩ := ready
      exact encodedLoad 8 false (by decide) projection (List.mem_singleton.mp routed) operands rfl rfl ⟨⟨lo, hi⟩, al⟩
    · rcases ready.2.2 with ⟨op, hi, lo, _⟩ | ⟨op, hi, lo, _⟩ | ⟨op, al, hi, lo, _⟩ |
        ⟨op, al, hi, lo, _⟩ | ⟨op, al, hi, lo, _⟩ | ⟨op, al, hi, lo, _⟩ | ⟨op, al, hi, lo, _⟩
      · exact encodedLoad 1 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, Nat.mod_one _⟩
      · exact encodedLoad 1 true (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, Nat.mod_one _⟩
      · exact encodedLoad 2 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 2 true (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 4 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 4 true (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
      · exact encodedLoad 8 false (by decide) projection op operands rfl rfl ⟨⟨lo, hi⟩, al⟩
    · let address : AddressOperation.Inputs (ZMod p) := ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1], input.offset_bit[2], input.is_real⟩
      apply encodedStore 1 (by decide) projection (List.mem_singleton.mp routed) operands rfl rfl
      exact storeSpan 1 (by decide) address ready.2.1 ready.2.2.1 (AddressOperation.validAddress_of_spec (spec.1.2.2.2 real))
        (Nat.mod_one _)
    · let address : AddressOperation.Inputs (ZMod p) := ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1], input.is_real⟩
      apply encodedStore 2 (by decide) projection (List.mem_singleton.mp routed) operands rfl rfl
      exact storeSpan 2 (by decide) address ready.2.1 ready.2.2.1 (AddressOperation.validAddress_of_spec (spec.1.2.2.2 real))
        (by simp [address, Nat.add_mod, Nat.mul_mod])
    · let address : AddressOperation.Inputs (ZMod p) := ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
      apply encodedStore 4 (by decide) projection (List.mem_singleton.mp routed) operands rfl rfl
      exact storeSpan 4 (by decide) address ready.2.1 ready.2.2.1 (AddressOperation.validAddress_of_spec (spec.1.2.2.2 real))
        (by simp [address])
    · let address : AddressOperation.Inputs (ZMod p) := ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
      apply encodedStore 8 (by decide) projection (List.mem_singleton.mp routed) operands rfl rfl
      exact storeSpan 8 (by decide) address ready.2.1 ready.2.2.1 (AddressOperation.validAddress_of_spec (spec.1.2.2.2 real))
        (by simp [address])
  · obtain ⟨op, member, same⟩ := List.mem_map.mp routed
    have outside : ∀ id : InstructionChipId,
        id ∉ [.loadByte, .loadHalf, .loadWord, .loadDouble, .loadX0, .storeByte, .storeHalf, .storeWord, .storeDouble] →
        ∀ op ∈ id.route.opcodes, op.toNat < 29 ∨ 39 < op.toNat := by
      intro i
      cases i <;> decide
    apply nonmemory projection
    rw [← same, ZMod.val_natCast_of_lt (lt_trans (opcode_toNat_lt _) (by have := Fact.out (p := 2 ^ 24 < p); omega))]
    exact outside id memory op member

/-- Physical decoding and grounded operands establish the complete ordinary encoding premise. -/
theorem DecodedInstructionRow.ordinaryEncodedAt (row : DecodedInstructionRow p)
    {data : ProverData (ZMod p)} {program : GuestProgram} {source : SailState}
    (fixed : DecodedRowStaticInputs row data) (dynamic : DecodedRowDynamicInputs row data program source)
    (real : (row.toChipRow data).is_real = 1)
    (decoded : decodedInROM program (programAccess (row.toChipRow data).view).toRow)
    (atPc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (row.toChipRow data).view).toRow)) :
    Semantics.ordinaryEncodedAt program source := by
  obtain ⟨word, instr, fetched, decode, projection⟩ := decoded
  obtain ⟨_, chip, _, routed⟩ := instrToProgramRow'_route_exists projection
  refine ⟨_, word, instr, atPc, fetched, decode, instructionImageOK_of_instrToProgramRow'_some projection,
    by simp only [routed, Option.isSome_some], ?_⟩
  have spec := fixed.chipSpec dynamic.circuit
  obtain ⟨chip, physical⟩ := row
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp fixed.registered
  exact supportedChipFor_memoryEncoded id _ _ data program source real spec dynamic.ready dynamic.operands projection

end SP1Clean.Soundness
