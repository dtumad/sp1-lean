import SP1Clean.Model.Semantics.SailArithmeticExecute

/-! # Circuit-independent arithmetic retirement and memory frames

Authenticated arithmetic decoding gives an actual normal Sail retirement that preserves the
platform configuration and entire memory map, including x0. The existing official execute-stage
lemmas supply the values; no native chip row or arithmetic constraints enter these statements.
Memory and control-flow instruction families require separate semantic proofs.
-/

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- Initialization supplies an actual value for every architectural GPR, including x0. -/
theorem initialized_gpr (source : SailState) (initialized : source.isInitialized) (index : BitVec 5) :
    ∃ value, source.get_reg? index = some value := by
  unfold SailState.get_reg?
  split_ifs
  · exact ⟨_, rfl⟩
  · refine ⟨cast (reg_idx_must_64 index) (source.regs.get _ (initialized _)), ?_⟩
    rw [Std.ExtDHashMap.get?_eq_some_get (initialized _)]
    simp only [eqRec_eq_cast]
    apply cast_eq_iff_heq.mpr
    congr 1
    · exact reg_idx_must_64 index
    · exact (cast_heq _ _).symm

/-- Staging the sequential successor does not change the platform configuration. -/
theorem SailConfigured.writeNextPC {source : SailState} (configured : SailConfigured source)
    (pc : BitVec 64) : SailConfigured { source with regs := source.regs.insert Register.nextPC pc } := by
  apply SailConfigured.congr configured (source.isInitialized_insert configured.init _ _)
  rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]

/-- A GPR write, or a discarded x0 write, preserves the platform configuration. -/
theorem SailConfigured.writeGPR {source : SailState} (configured : SailConfigured source)
    (rd : BitVec 5) (value : BitVec 64) :
    SailConfigured (if rd = 0 then source else
      { source with regs := source.regs.insert (reg_idx_to_Register rd) (bitVecToRegidxVal rd value) }) := by
  split_ifs
  · exact configured
  · apply SailConfigured.congr configured (source.isInitialized_insert configured.init _ _)
    rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rw [Std.ExtDHashMap.get?_insert, dif_neg (by unfold reg_idx_to_Register; split <;> decide)]

/-- Compose a circuit-independent execute-stage frame with the official retirement tail.
This helper's execute premise is discharged for each family below; it is not a capstone premise. -/
theorem retire_frame_of_execute {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (executeFrame : ∀ state, SailConfigured state → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨increment, incrementRun⟩ : ∃ increment,
      (should_inc_minstret Privilege.Machine).run source = .ok increment source :=
    ⟨_, run_should_inc_minstret source configured.init _⟩
  let marked : SailState := {source with regs := source.regs.insert Register.minstret_increment increment}
  have markedCfg : SailConfigured marked := SailConfigured.writeMinstret configured increment
  have ready : StraightLineReady marked word := by
    simpa only [word_reassemble] using SailConfigured.toStraightLineReady configured increment pc _ _ _ _
      (fetchReady_of_romLoaded program source pc word loaded fetched atPc)
  let nextPc := BitVec.addInt (marked.regs.get Register.PC (ready.init _)) 4
  let staged : SailState := {marked with regs := marked.regs.insert Register.nextPC nextPc}
  have stagedCfg : SailConfigured staged := SailConfigured.writeNextPC markedCfg _
  obtain ⟨post, executed, postCfg, memory⟩ := executeFrame staged stagedCfg
  obtain ⟨actual, _, normal, _, _, sameMemory, registerFrame, initialized, _⟩ :=
    sailStep_of_ladder_bookkeeping source staged post word decoded increment incrementRun
      (by rw [Sail.run_readReg, configured.priv]) markedCfg.active ready (decode marked markedCfg)
      (by rw [Sail.run_writeReg]) executed postCfg.active postCfg.init
  refine ⟨actual, normal, ?_, sameMemory.trans memory⟩
  apply SailConfigured.congr postCfg initialized
  rintro register (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact registerFrame _ (by decide) (by decide)

/-- Arithmetic constructors whose execute stage writes at most one GPR. This is a proof
classification of Sail instructions, not the native supported-program or resource profile. -/
def ArithmeticInstruction : instruction → Prop
  | .RTYPE _ => True
  | .RTYPEW _ => True
  | .ITYPE _ => True
  | .SHIFTIOP _ => True
  | .SHIFTIWOP _ => True
  | .ADDIW _ => True
  | .UTYPE _ => True
  | .DIV _ => True
  | .REM _ => True
  | .DIVW _ => True
  | .REMW _ => True
  | .MUL _ => True
  | .MULW _ => True
  | _ => False

/-- Every arithmetic execute stage preserves the platform configuration and complete memory,
including the x0 and signed/unsigned multiply/divide cases. No chip witness is constructed. -/
theorem arithmetic_execute_frame (state : SailState) (cfg : SailConfigured state)
    (decoded : instruction) (arithmetic : ArithmeticInstruction decoded) : ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem := by
  unfold ArithmeticInstruction at arithmetic
  split at arithmetic
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, rtype_execute_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, rtypew_execute_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, itype_execute_reaches imm rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨shamt, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, shiftitype_execute_reaches shamt rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨shamt, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, shiftiwtype_execute_reaches shamt rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, execute_ADDIW_reaches imm rs1 rd left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rd⟩, op⟩
    exact ⟨_, execute_UTYPE_reaches imm rd op _ state (Std.ExtDHashMap.get?_eq_some_get (cfg.init _)),
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_DIV_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_REM_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_DIVW_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_REMW_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_MUL_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_MULW_reaches rs2 rs1 rd left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next => contradiction

/-- Authenticated arithmetic instructions actually retire normally, without requiring another
instruction at the outgoing PC. Configuration and the whole byte map are preserved. -/
theorem arithmetic_retire {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (arithmetic : ArithmeticInstruction decoded) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ target.mem = source.mem :=
  retire_frame_of_execute configured loaded atPc fetched decode
    (fun state cfg => arithmetic_execute_frame state cfg decoded arithmetic)

/-- Every actual normal retirement agrees with the constructed arithmetic successor. -/
theorem arithmetic_normal_frame {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (arithmetic : ArithmeticInstruction decoded) (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨actual, retired, frame⟩ := arithmetic_retire configured loaded atPc fetched decode arithmetic
  obtain ⟨_, _, _, _, _, actualRun⟩ := retired
  obtain ⟨_, _, _, _, _, targetRun⟩ := normal
  rw [actualRun] at targetRun
  cases targetRun
  exact frame

end SP1Clean.Advance
