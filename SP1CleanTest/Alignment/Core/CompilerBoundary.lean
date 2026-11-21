import SP1Clean.Math.SP1Field
import SP1Clean.Proofs.Chips.BranchChip.Complete
import SP1Clean.Proofs.Chips.JalChip.Complete
import SP1Clean.Proofs.Chips.JalrChip.Complete
import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Semantics.Execution.ConfiguredState
import SP1Clean.Semantics.Sail.SailControlExecute

/-! # Control-flow compiler boundaries

A last-slot JAL retires at the official Sail execute stage with a link at 2^48. The x0 form
discards its link, while a nonzero destination enables native link arithmetic. Branch fixtures
build accepted Clean tables at both selected ends of the PC window and check that out-of-window
selected destinations fail their event contract.
-/

namespace SP1CleanTest.Core.CompilerBoundary
open SP1Clean SP1Clean.Semantics SP1Clean.Soundness.Target
open SP1Clean.TraceGen LeanRV64D LeanRV64D.Functions

private def lastPc : BitVec 64 := BitVec.ofNat 64 (2 ^ 48 - 4)

private def image : ProgramImage := ⟨[(lastPc, 0x000000EF)], lastPc, []⟩

/-- The checked loader accepts the final four-byte instruction slot, including JAL x1, 0. -/
theorem lastSlot_image_valid : image.Valid := by native_decide

private def staged (pc : BitVec 64) : SailState :=
  { configuredState pc with regs := (configuredState pc).regs.insert Register.nextPC (pc + 4#64) }

private theorem staged_initialized (pc : BitVec 64) : (staged pc).isInitialized :=
  SailState.isInitialized_insert _ (cfgState_init pc) _ _

private theorem staged_pc (pc : BitVec 64) : (staged pc).regs.get? Register.PC = some pc := by
  change ((configuredState pc).regs.insert Register.nextPC (pc + 4#64)).get? Register.PC = some pc
  rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide)]
  exact cfgState_pc pc

private def jalTarget (rd : BitVec 5) : SailState :=
  if rd = 0 then
    { staged lastPc with regs := (staged lastPc).regs.insert Register.nextPC lastPc }
  else
    { staged lastPc with regs := (((staged lastPc).regs.insert Register.nextPC lastPc).insert
      (reg_idx_to_Register rd) (bitVecToRegidxVal rd (lastPc + 4#64))) }

/-- Official Sail JAL execute succeeds for every destination at the top instruction slot.
In particular Sail does not require the link value to be a 48-bit program counter. -/
theorem lastSlot_jal_executes (rd : BitVec 5) :
    (runSail (execute (.JAL (0, .Regidx rd)))) (staged lastPc) =
      .ok (.Retire_Success ()) (jalTarget rd) := by
  exact Advance.execute_JAL_reaches 0 rd lastPc (staged lastPc)
      (staged_initialized lastPc) (staged_pc lastPc)
      (by simp only [staged, Std.ExtDHashMap.get?_insert_self]) (by decide)

private def lastEvent (rd : ℕ) : JTypeEvent where
  clk := 1
  pc := 2 ^ 48 - 4
  opcode := Soundness.Opcode.JAL.toNat
  opA := rd
  immB := 0
  immC := 0
  prevA := 0
  prevTsA := 0

private def compiledJal (rd : BitVec 5) : Option CompiledInstructionEvent :=
  compileInstructionEvent?
    ⟨lastPc, if rd = 0 then 0x0000006F else 0x000000EF,
      .JAL (0, .Regidx rd), ⟨.JAL, decide (rd = 0)⟩, .jal,
      instructionAccessPlan? (.JAL (0, .Regidx rd)) (staged lastPc) (jalTarget rd)⟩
    AccessFrontier.initial 1

private def jalFields (event : JTypeEvent) : List ℕ :=
  [event.clk, event.pc, event.opcode, event.opA, event.immB, event.immC, event.prevA, event.prevTsA]

private def compiledJalFields (rd : BitVec 5) : Option (List ℕ) := do
  let result ← compiledJal rd
  let event ← result.routed.forId? .jal
  pure (jalFields event)

/-- The actual compiler applied to the same official-execute source/target pairs emits all eight
fields of the rejected event for both the discarded and enabled link forms. -/
theorem lastSlot_compiled_events :
    (compiledJalFields 0, compiledJalFields 1) =
      (some (jalFields (lastEvent 0)), some (jalFields (lastEvent 1))) := by
  native_decide

/-- All ordinary JAL event fields are valid for both x0 and a genuine link destination. -/
theorem lastEvent_wellFormed (rd : ℕ) (small : rd < 32) : (lastEvent rd).WellFormedJal := by
  constructor <;> simp [lastEvent]
  exact small

/-- The actual self-jump destination is representable and aligned. Only the link condition fails. -/
theorem lastEvent_target (rd : ℕ) :
    (lastEvent rd).jalTarget < 2 ^ 48 ∧ (lastEvent rd).jalTarget % 4 = 0 := by
  norm_num [lastEvent, JTypeEvent.jalTarget]

/-- At the last fetch slot an enabled link would be 2^48. Selecting x0 disables that link. -/
theorem lastEvent_valid_iff (rd : ℕ) : InstructionChipId.jal.Valid (lastEvent rd) ↔ rd = 0 := by
  constructor
  · intro valid
    by_contra writes
    have bound := valid.2.2.2 writes
    norm_num [lastEvent] at bound
  · rintro rfl
    exact ⟨lastEvent_wellFormed 0 (by decide), (lastEvent_target 0).1, (lastEvent_target 0).2,
      fun writes => (writes rfl).elim⟩

private def lastJalr (rd : ℕ) : ITypeEvent :=
  ⟨1, 2 ^ 48 - 4, Soundness.Opcode.JALR.toNat, rd, 1, 0, 2 ^ 48 - 4, 0, 0, 0⟩

/-- On the last fetch slot JALR can discard the link while jumping back to itself. -/
theorem lastJalr_targets_iff (rd : ℕ) : (lastJalr rd).JalrTargets ↔ rd = 0 := by
  simp [ITypeEvent.JalrTargets, ITypeEvent.jalrTarget, JumpLinkFits, lastJalr]

/-- Both discarded-link events supply their actual Clean chip's honest-prover contract. -/
theorem lastSlot_discardedLinks (data : ProverData (ZMod SP1Prime)) (hint : ProverHint (ZMod SP1Prime)) :
    JalChip.ProverAssumptions (lastEvent 0).toJalInputs data hint ∧
      JalrChip.ProverAssumptions (lastJalr 0).toJalrInputs data hint := by
  obtain ⟨well, targets⟩ := (lastEvent_valid_iff 0).mpr rfl
  exact ⟨JalChip.proverAssumptions_of_event well targets data hint,
    JalrChip.proverAssumptions_of_event (by constructor <;> decide) ((lastJalr_targets_iff 0).mpr rfl) data hint⟩

private def untakenEvent : ITypeEvent where
  clk := 1
  pc := 2 ^ 48 - 8
  opcode := 41
  opA := 0
  opB := 0
  imm := 16
  b := 0
  prevA := 0
  prevTsA := 4
  prevTsB := 0

/-- BNE x0, x0, +16 at the edge of guest memory falls through to a valid native PC. Its
unselected candidate exceeds the PC window and the actual branch row still satisfies its
honest-prover assumptions. -/
theorem untakenBranch_selected_valid :
    untakenEvent.branchTaken = false ∧ 2 ^ 48 ≤ untakenEvent.branchTarget ∧
      untakenEvent.WellFormedBranch ∧ untakenEvent.IsBranch ∧ untakenEvent.BranchTargets := by
  refine ⟨by native_decide, by native_decide, ?_, ?_, ?_⟩
  · constructor <;> native_decide
  · unfold ITypeEvent.IsBranch
    native_decide
  · unfold ITypeEvent.BranchTargets
    native_decide

private def takenEvent : ITypeEvent :=
  {untakenEvent with pc := 2 ^ 48 - 4, opcode := 40, imm := 0}

/-- BEQ x0, x0, 0 can take its self-jump from the final fetch slot. The unused link is 2^48. -/
theorem takenBranch_selected_valid :
    takenEvent.branchTaken = true ∧ 2 ^ 48 = takenEvent.pc + 4 ∧
      takenEvent.WellFormedBranch ∧ takenEvent.IsBranch ∧ takenEvent.BranchTargets := by
  refine ⟨by native_decide, by native_decide, ?_, ?_, ?_⟩
  · constructor <;> native_decide
  · unfold ITypeEvent.IsBranch
    native_decide
  · unfold ITypeEvent.BranchTargets
    native_decide

/-- Each branch direction still rejects a selected destination outside the native PC word. -/
theorem branch_selected_overflow_invalid :
    ¬ ({untakenEvent with opcode := 40} : ITypeEvent).BranchTargets ∧
      ¬ ({takenEvent with opcode := 41} : ITypeEvent).BranchTargets := by
  unfold ITypeEvent.BranchTargets
  native_decide

/-- Clean builds a constrained and channel-valid table for both 48-bit-edge branch directions. -/
theorem edgeBranch_table_valid :
    let events := [untakenEvent, takenEvent]
    let inputs := BranchChip.traceInputs (p := SP1Prime) events 0
    let data : ProverData (ZMod SP1Prime) := (BranchChip.component (p := SP1Prime)).inputData inputs (.empty _)
    let table := Air.Flat.Table.build (BranchChip.component (p := SP1Prime)) inputs data (ProverHint.empty _) (by decide)
      (by trivial) ((BranchChip.component (p := SP1Prime)).inputData_consistent _ _)
    table.Constraints ∧ table.Guarantees := by
  have valid : ∀ e ∈ [untakenEvent, takenEvent], e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets := by
    intro e member
    rcases List.mem_cons.mp member with rfl | later
    · exact untakenBranch_selected_valid.2.2
    · obtain rfl := List.mem_singleton.mp later
      exact takenBranch_selected_valid.2.2
  exact ⟨BranchChip.traceTable_constraints (p := SP1Prime) _ 0 _ valid (by decide) _,
    BranchChip.traceTable_guarantees (p := SP1Prime) _ 0 _ valid (by decide) _⟩

/-- Official Sail also executes that untaken branch: no target-address check is imposed on the
candidate that the instruction does not select. -/
theorem untakenBranch_executes :
    ∃ target, (runSail (execute (.BTYPE (16, .Regidx 0, .Regidx 0, .BNE))))
      (staged (BitVec.ofNat 64 (2 ^ 48 - 8))) = .ok (.Retire_Success ()) target := by
  exact ⟨_, Advance.execute_BTYPE_reaches 16 0 0 .BNE _ _ 0 0 _
    (staged_initialized _) (staged_pc _)
    (by simp only [staged, Std.ExtDHashMap.get?_insert_self])
    (by simp [SailState.get_reg?]) (by simp [SailState.get_reg?])
    (by decide) (fun _ => rfl) (by decide)⟩

end SP1CleanTest.Core.CompilerBoundary
