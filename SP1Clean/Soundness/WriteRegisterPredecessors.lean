import SP1Clean.Math.SP1Field
import SP1Clean.Soundness.ChipContracts

/-! # Register predecessors in the original ordinary instruction ledgers

The descriptor's normalized adapter selects the actual A/B/C register inputs. Its immediate
selectors suppress the corresponding register pulls. RAM instructions also have an independent
RAM transfer, which stays in their full original ledger.
-/

namespace SP1Clean.WriteProbe.OrdinarySources

open Circuit Air.Flat Soundness Channels

private abbrev F := ZMod SP1Prime

/-- The register messages present on an active physical instruction, in original A/B/C order. -/
def registerPriors (view : Trace.RowView F) : List (MemoryMsg F) :=
  [rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory] ++
    (if view.adapter.imm_b = 0 then [rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory] else []) ++
    (if view.adapter.imm_c = 0 then [rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory] else [])

private theorem rType_registers {chip : SupportedChip SP1Prime} (shape : RTypeMemoryInteractionShape chip)
    (row : DecodedInstructionRow SP1Prime) (data : ProverData F) (chipEq : row.chip = chip)
    (real : (row.toChipRow data).view.is_real = 1) :
    ∀ m ∈ registerPriors (row.toChipRow data).view, m ∈ row.consumedMemoryMessages data := by
  rw [consumedMemoryMessages_eq_of_rtypeShape shape row data chipEq real]
  intro m used
  unfold registerPriors at used
  split at used <;> split at used <;> simp_all only [List.append_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  all_goals tauto

private theorem iType_registers {view : Trace.RowView F} {list : List (MemoryMsg F)}
    (noC : view.adapter.imm_c = 1)
    (shape : list = [rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory]) :
    ∀ m ∈ registerPriors view, m ∈ list := by
  subst list
  intro m used
  simp only [registerPriors, noC, one_ne_zero, ↓reduceIte, List.append_nil] at used
  split at used <;> simp_all only [List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  all_goals tauto

private theorem jType_registers {view : Trace.RowView F} {list : List (MemoryMsg F)}
    (noB : view.adapter.imm_b = 1) (noC : view.adapter.imm_c = 1)
    (shape : list = [rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory]) :
    ∀ m ∈ registerPriors view, m ∈ list := by
  simpa only [registerPriors, noB, noC, one_ne_zero, ↓reduceIte, List.append_nil, shape] using
    (fun (m : MemoryMsg F) (h : m ∈ [rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory]) => h)

private theorem ram_registers {view : Trace.RowView F} {list : List (MemoryMsg F)} {ram : MemoryMsg F}
    (noC : view.adapter.imm_c = 1)
    (shape : list = [ram, rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory,
      rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory]) :
    ∀ m ∈ registerPriors view, m ∈ list := by
  intro m used
  rw [shape]
  exact List.mem_cons_of_mem _ (iType_registers noC rfl _ used)

private theorem alu_registers {row : DecodedInstructionRow SP1Prime} {data : ProverData F}
    (binary : (row.toChipRow data).view.adapter.imm_c = 0 ∨ (row.toChipRow data).view.adapter.imm_c = 1)
    (reg : (row.toChipRow data).view.adapter.imm_c = 0 →
      let v := (row.toChipRow data).view
      row.consumedMemoryMessages data = [rtypePriorMessage v v.adapter.op_a v.adapter.op_a_memory,
        rtypePriorMessage v v.adapter.op_b[0] v.adapter.op_b_memory, rtypePriorMessage v v.adapter.op_c[0] v.adapter.op_c_memory])
    (immediate : (row.toChipRow data).view.adapter.imm_c = 1 →
      let v := (row.toChipRow data).view
      row.consumedMemoryMessages data = [rtypePriorMessage v v.adapter.op_a v.adapter.op_a_memory,
        rtypePriorMessage v v.adapter.op_b[0] v.adapter.op_b_memory]) :
    ∀ m ∈ registerPriors (row.toChipRow data).view, m ∈ row.consumedMemoryMessages data := by
  rcases binary with c | c
  · intro m used
    rw [reg c]
    simp only [registerPriors, c, ↓reduceIte] at used
    split at used <;> simp_all only [List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    all_goals tauto
  · exact iType_registers c (immediate c)

/-- Every active register prior selected by the installed chip is present in its original
unit-weight Memory pulls. Works on generated arrays at arbitrary physical evaluation data. -/
theorem registerPriors_consumed (id : InstructionChipId) (row : DecodedInstructionRow SP1Prime) (data : ProverData F) (registered : row.chip = supportedChipFor id)
    (checked : row.chip.table.operations.ConstraintsHold (row.environment data))
    (real : (row.toChipRow data).view.is_real = 1)
    (binary : (row.toChipRow data).view.adapter.imm_c = 0 ∨ (row.toChipRow data).view.adapter.imm_c = 1) :
    ∀ m ∈ registerPriors (row.toChipRow data).view, m ∈ row.consumedMemoryMessages data := by
  obtain ⟨chip, physical⟩ := row
  dsimp only at registered
  subst chip
  cases id with
  | add => exact rType_registers addChip_rtypeMemoryInteractionShape _ _ rfl real
  | sub => exact rType_registers subChip_rtypeMemoryInteractionShape _ _ rfl real
  | subw => exact rType_registers subwChip_rtypeMemoryInteractionShape _ _ rfl real
  | mul => exact rType_registers mulChip_rtypeMemoryInteractionShape _ _ rfl real
  | divRem => exact rType_registers divRemChip_rtypeMemoryInteractionShape _ _ rfl real
  | addi => exact iType_registers rfl (consumedMemoryMessages_eq_of_itypeShape addiChip_itypeMemoryInteractionShape _ _ rfl real)
  | jalr => exact iType_registers rfl (consumedMemoryMessages_eq_of_itypeShape jalrChip_itypeMemoryInteractionShape _ _ rfl real)
  | branch => exact iType_registers rfl (consumedMemoryMessages_eq_of_immutableItypeShape branchChip_immutableItypeMemoryInteractionShape _ _ rfl real)
  | jal => exact jType_registers rfl rfl (consumedMemoryMessages_eq_of_jtypeShape jalChip_jtypeMemoryInteractionShape _ _ rfl real)
  | uType => exact jType_registers rfl rfl (consumedMemoryMessages_eq_of_jtypeShape uTypeChip_jtypeMemoryInteractionShape _ _ rfl real)
  | addw =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_aluType_register addwChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
      (consumedMemoryMessages_eq_of_aluType_immediate addwChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
  | bitwise =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_aluType_register bitwiseChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
      (consumedMemoryMessages_eq_of_aluType_immediate bitwiseChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
  | lt =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_aluType_register ltChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
      (consumedMemoryMessages_eq_of_aluType_immediate ltChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
  | shiftLeft =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_aluType_register shiftLeftChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
      (consumedMemoryMessages_eq_of_aluType_immediate shiftLeftChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
  | shiftRight =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_aluType_register shiftRightChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
      (consumedMemoryMessages_eq_of_aluType_immediate shiftRightChip_aluTypeMemoryInteractionShape.constrained _ _ rfl checked real)
  | aluX0 =>
    exact alu_registers binary (consumedMemoryMessages_eq_of_immutableAlu_register aluX0Chip_immutableALUTypeMemoryInteractionShape _ _ rfl real)
      (consumedMemoryMessages_eq_of_immutableAlu_immediate aluX0Chip_immutableALUTypeMemoryInteractionShape _ _ rfl real)
  | loadByte => exact ram_registers rfl (consumedMemoryMessages_eq_of_loadShape loadByteChip_loadMemoryInteractionShape _ _ rfl real)
  | loadHalf => exact ram_registers rfl (consumedMemoryMessages_eq_of_loadShape loadHalfChip_loadMemoryInteractionShape _ _ rfl real)
  | loadWord => exact ram_registers rfl (consumedMemoryMessages_eq_of_loadShape loadWordChip_loadMemoryInteractionShape _ _ rfl real)
  | loadDouble => exact ram_registers rfl (consumedMemoryMessages_eq_of_loadShape loadDoubleChip_loadMemoryInteractionShape _ _ rfl real)
  | loadX0 => exact ram_registers rfl (consumedMemoryMessages_eq_of_immutableRamShape loadX0Chip_immutableRamMemoryInteractionShape _ _ rfl real)
  | storeByte => exact ram_registers rfl (consumedMemoryMessages_eq_of_immutableRamShape storeByteChip_immutableRamMemoryInteractionShape _ _ rfl real)
  | storeHalf => exact ram_registers rfl (consumedMemoryMessages_eq_of_immutableRamShape storeHalfChip_immutableRamMemoryInteractionShape _ _ rfl real)
  | storeWord => exact ram_registers rfl (consumedMemoryMessages_eq_of_immutableRamShape storeWordChip_immutableRamMemoryInteractionShape _ _ rfl real)
  | storeDouble => exact ram_registers rfl (consumedMemoryMessages_eq_of_immutableRamShape storeDoubleChip_immutableRamMemoryInteractionShape _ _ rfl real)

end SP1Clean.WriteProbe.OrdinarySources
