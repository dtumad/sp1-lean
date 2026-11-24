module

public import SP1Clean.Semantics.Sail.SailExecuteFrame
import SP1Clean.Semantics.Sail.SailExecuteDispatch

/-! # Circuit-independent control-flow preservation

JAL, JALR and all six branch conditions preserve the configured platform and full memory map.
The proof recovers the actual execute stage of a normal retirement; jump alignment and successful
execution are not additional premises. Trap outcomes cannot masquerade as normal retirement.
-/

@[expose] public section

namespace SP1Clean.BranchSail
open LeanRV64D

/-- The decoded RISC-V branch condition on the two architectural register values. -/
def branchCond (op : bop) (x y : BitVec 64) : Prop :=
  match op with
  | .BEQ => x = y
  | .BNE => x ≠ y
  | .BLT => x.slt y = true
  | .BGE => x.slt y = false
  | .BLTU => x.ult y = true
  | .BGEU => x.ult y = false

end SP1Clean.BranchSail

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ArchSem LeanRV64D LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- A control-flow successor register contains the selected four-byte-aligned address. -/
def AlignedPC (observed : Option (BitVec 64)) (destination : BitVec 64) : Prop :=
  observed = some destination ∧ destination.toNat % 4 = 0

private theorem jump_alignment (destination : BitVec 64)
    (low : (BitVec.access destination 0 == 0#1) = true)
    (high : bit_to_bool (BitVec.access destination 1) = false) : destination.toNat % 4 = 0 := by
  have bit0 : destination[0] = false := by
    cases h : destination[0] <;> simp [BitVec.access, h] at low ⊢
  have bit1 : destination[1] = false := by
    cases h : destination[1] <;> simp [BitVec.access, h, bit_to_bool, bool_bit_backwards] at high ⊢
  simp only [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_false_iff_not] at bit0 bit1
  omega

private theorem fetched_pc_add_four_aligned {program : GuestProgram} {pc : BitVec 64} {word : BitVec 32}
    (fetched : program.fetchWord pc = some word) : (pc + 4#64).toNat % 4 = 0 := by
  obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
  have same : entry.1 = pc := by simpa only [beq_iff_eq] using List.find?_some found
  have aligned := program.rom_aligned entry.1 (List.mem_map_of_mem (List.mem_of_find?_eq_some found))
  rw [same] at aligned
  rw [BitVec.toNat_add]
  change ((pc.toNat + 4) % 2 ^ 64) % 4 = 0
  omega

/-- A jump either traps or stages its destination, preserving configuration and all memory. -/
theorem jump_to_frame (source : SailState) (cfg : SailConfigured source) (destination : BitVec 64)
    (result : ExecutionResult) (target : SailState)
    (ran : (runSail (jump_to destination)) source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem ∧ Semantics.DestinationFrame none source target ∧
      (result = .Retire_Success () → AlignedPC (target.regs.get? Register.nextPC) destination) := by
  simp only [jump_to, ext_control_check_pc, SailME.run, PreSail.PreSailME.run_lift_bind] at ran
  by_cases low : (BitVec.access destination 0 == 0#1) = true
  · simp only [PreSail.sail_assert, low, ↓reduceIte, pure_bind, andM, toBool] at ran
    cases misaligned : bit_to_bool (BitVec.access destination 1) with
    | false =>
      simp only [misaligned, pure_bind, Bool.false_eq_true, ite_false] at ran
      rw [PreSail.PreSailME.run_lift_bind, PreSail.PreSailME.run_pure] at ran
      simp only [set_next_pc] at ran
      cases ran
      exact ⟨(fun _ h => nomatch h), SailConfigured.writeNextPC cfg _, rfl, writeNextPC_frame _ _, fun _ => ⟨Std.ExtDHashMap.get?_insert_self .., jump_alignment destination low misaligned⟩⟩
    | true =>
      simp only [misaligned, pure_bind, bind_assoc, PreSail.PreSailME.run_lift_bind] at ran
      rw [run_bind_of_run source (FreeM.pure ()) () rfl,
        run_bind_of_run source _ _ (currentlyEnabled_zca_eq_false source cfg)] at ran
      simp only [LeanRV64D.not, Bool.not_false, ite_true] at ran
      simp only [exception_context, inVirtualPrivilege, bind_assoc, pure_bind,
        PreSail.PreSailME.run_lift_bind, PreSail.PreSailME.run_lift, trap] at ran
      rw [run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init] at ran
      rw [run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
        run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
      cases ran
      exact ⟨(fun _ h => nomatch h), cfg, rfl, (.refl _), fun h => nomatch h⟩
  · simp only [PreSail.sail_assert, low, bind] at ran
    cases ran

private theorem jump_and_link_frame (source : SailState) (cfg : SailConfigured source)
    (destination link : BitVec 64) (rd : BitVec 5) (result : ExecutionResult) (target : SailState)
    (ran : (runSail (do
      match ← jump_to destination with
      | .Retire_Success () => wX_bits (.Regidx rd) link; pure (ExecutionResult.Retire_Success ())
      | failure => pure failure)) source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem ∧ Semantics.DestinationFrame (some rd) source target ∧
      (result = .Retire_Success () → AlignedPC (target.regs.get? Register.nextPC) destination) := by
  obtain ⟨middle, outcome, jumpRun, suffix⟩ := run_bind_success _ _ source target result ran
  obtain ⟨direct, configured, memory, framed, staged⟩ := jump_to_frame source cfg destination outcome middle jumpRun
  by_cases success : outcome = .Retire_Success ()
  · subst outcome
    rw [run_bind_of_run' middle _ _ () (run_wX_bits (.Regidx rd) link)] at suffix
    cases suffix
    exact ⟨(fun _ h => nomatch h), SailConfigured.writeGPR configured rd link, by
      by_cases zero : rd = 0#5 <;> simpa only [zero, ↓reduceIte] using memory,
      (Semantics.DestinationFrame.of_none framed (some rd)).trans (writeGPR_frame middle rd link),
      fun _ => ⟨(writeGPR_nextPC middle rd link).trans (staged rfl).1, (staged rfl).2⟩⟩
  · cases outcome <;> first | contradiction | (cases suffix; exact ⟨direct, configured, memory, Semantics.DestinationFrame.of_none framed _, staged⟩)

/-- JAL preserves configuration and every byte for every successful execute result. -/
theorem jal_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 21) (rd : BitVec 5) (result : ExecutionResult) (target : SailState)
    (ran : (runSail (execute (.JAL (imm, .Regidx rd)))) source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem ∧ Semantics.DestinationFrame (some rd) source target ∧
      (result = .Retire_Success () → AlignedPC (target.regs.get? Register.nextPC)
        (source.regs.get Register.PC (cfg.init _) + sign_extend (m := 64) imm)) := by
  simp only [SailExecute.dispatch_JAL, execute_JAL, get_next_pc] at ran
  rw [run_readReg_bind_of_isInitialized source Register.nextPC cfg.init,
    run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
  exact jump_and_link_frame source cfg _ _ rd result target ran

/-- JALR preserves configuration and every byte, using Sail’s masked target and ELP handling. -/
theorem jalr_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (value : BitVec 64) (read : source.get_reg? rs1 = some value)
    (result : ExecutionResult) (target : SailState)
    (ran : (runSail (execute (.JALR (imm, .Regidx rs1, .Regidx rd)))) source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem ∧ Semantics.DestinationFrame (some rd) source target ∧
      (result = .Retire_Success () → AlignedPC (target.regs.get? Register.nextPC)
        (BitVec.update (value + sign_extend (m := 64) imm) 0 0#1)) := by
  simp only [SailExecute.dispatch_JALR, execute_JALR, get_next_pc] at ran
  rw [run_bind_of_run source _ () (SailMem.update_elp_state_of_isInitialized _ source cfg.init cfg.toValidMemConfig),
    run_readReg_bind_of_isInitialized source Register.nextPC cfg.init,
    run_bind_of_run source _ value (by rw [run_rX_bits, read])] at ran
  simp only [pure_bind] at ran
  exact jump_and_link_frame source cfg _ _ rd result target ran

/-- Every branch condition preserves configuration and every byte, taken or not taken. -/
theorem branch_execute_frame (source : SailState) (cfg : SailConfigured source)
    (imm : BitVec 13) (rs1 rs2 : BitVec 5) (op : bop) (left right : BitVec 64) (leftRead : source.get_reg? rs1 = some left) (rightRead : source.get_reg? rs2 = some right)
    (result : ExecutionResult) (target : SailState)
    (ran : (runSail (execute (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)))) source = .ok result target) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured target ∧ target.mem = source.mem ∧ Semantics.DestinationFrame none source target ∧
      (result = .Retire_Success () →
        (BranchSail.branchCond op left right → AlignedPC (target.regs.get? Register.nextPC)
          (source.regs.get Register.PC (cfg.init _) + sign_extend (m := 64) imm)) ∧
        (¬ BranchSail.branchCond op left right → target.regs.get? Register.nextPC = source.regs.get? Register.nextPC)) := by
  have leftRun : (runSail (rX_bits (.Regidx rs1))) source = .ok left source := by rw [run_rX_bits, leftRead]
  have rightRun : (runSail (rX_bits (.Regidx rs2))) source = .ok right source := by rw [run_rX_bits, rightRead]
  cases op <;>
    simp only [SailExecute.dispatch_BTYPE, execute_BTYPE, bind_assoc,
      run_bind_of_run source _ left leftRun, run_bind_of_run source _ right rightRun, pure_bind] at ran
  all_goals
    split at ran
    · rename_i taken
      rw [run_readReg_bind_of_isInitialized source Register.PC cfg.init] at ran
      obtain ⟨direct, afterCfg, memory, framed, staged⟩ := jump_to_frame source cfg _ result target ran
      refine ⟨direct, afterCfg, memory, framed, fun success => ⟨fun _ => staged success, fun notTaken => False.elim (notTaken ?_)⟩⟩
      simpa [BranchSail.branchCond, zopz0zI_s, zopz0zKzJ_s, zopz0zI_u, zopz0zKzJ_u,
        BitVec.slt, BitVec.ult, Sail.BitVec.toNatInt] using taken
    · rename_i notTaken
      cases ran
      refine ⟨(fun _ h => nomatch h), cfg, rfl, (.refl _), fun _ => ⟨fun taken => False.elim (notTaken ?_), fun _ => rfl⟩⟩
      simpa [BranchSail.branchCond, zopz0zI_s, zopz0zKzJ_s, zopz0zI_u, zopz0zKzJ_u,
        BitVec.slt, BitVec.ult, Sail.BitVec.toNatInt] using taken

/-- A normally retired JAL commits the official wrapped, sign-extended target even with rd=x0. -/
theorem jal_normal_successor {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {imm : BitVec 21} {rd : BitVec 5}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (decode : ConfiguredDecode word (.JAL (imm, .Regidx rd))) (normal : SailRetiresNormally source target) :
    AlignedPC (target.regs.get? Register.PC) (pc + sign_extend (m := 64) imm) := by
  obtain ⟨_, _, _, successor, _⟩ := normal_observed_direct_execute configured loaded atPc fetched decode
    (fun _ => True) (fun result => AlignedPC result (pc + sign_extend (m := 64) imm))
    (fun state cfg _ _ current _ result next ran => by
      obtain ⟨direct, afterCfg, _, _, staged⟩ := jal_execute_frame state cfg imm rd result next ran
      have pcEq : state.regs.get Register.PC (cfg.init _) = pc := by
        rwa [Std.ExtDHashMap.get?_eq_some_get (cfg.init _), Option.some.injEq] at current
      exact ⟨direct, afterCfg, trivial, fun success => by simpa only [pcEq] using staged success⟩) normal
  exact successor

/-- A normally retired JALR commits the masked, wrapped register-relative target, including
the case in which source and destination are the same GPR. -/
theorem jalr_normal_successor {program : GuestProgram} {source target : SailState}
    {pc value : BitVec 64} {word : BitVec 32} {imm : BitVec 12} {rs1 rd : BitVec 5}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (read : source.get_reg? rs1 = some value)
    (decode : ConfiguredDecode word (.JALR (imm, .Regidx rs1, .Regidx rd)))
    (normal : SailRetiresNormally source target) :
    AlignedPC (target.regs.get? Register.PC) (BitVec.update (value + sign_extend (m := 64) imm) 0 0#1) := by
  obtain ⟨_, _, _, successor, _⟩ := normal_observed_direct_execute configured loaded atPc fetched decode
    (fun _ => True) (fun result => AlignedPC result (BitVec.update (value + sign_extend (m := 64) imm) 0 0#1))
    (fun state cfg registers _ _ _ result next ran => by
      obtain ⟨direct, afterCfg, _, _, staged⟩ := jalr_execute_frame state cfg imm rs1 rd value
        ((registers rs1).trans read) result next ran
      exact ⟨direct, afterCfg, trivial, staged⟩) normal
  exact successor

/-- A normally retired branch commits precisely the selected target. The unselected address
has no alignment or representability premise. -/
theorem branch_normal_successor {program : GuestProgram} {source target : SailState}
    {pc left right : BitVec 64} {word : BitVec 32} {imm : BitVec 13} {rs1 rs2 : BitVec 5} {op : bop}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (read1 : source.get_reg? rs1 = some left) (read2 : source.get_reg? rs2 = some right)
    (decode : ConfiguredDecode word (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)))
    (normal : SailRetiresNormally source target) :
    (BranchSail.branchCond op left right → AlignedPC (target.regs.get? Register.PC) (pc + sign_extend (m := 64) imm)) ∧
      (¬ BranchSail.branchCond op left right → AlignedPC (target.regs.get? Register.PC) (pc + 4#64)) := by
  obtain ⟨_, _, _, successor, _⟩ := normal_observed_direct_execute configured loaded atPc fetched decode
    (fun _ => True) (fun result => (BranchSail.branchCond op left right → AlignedPC result (pc + sign_extend (m := 64) imm)) ∧
      (¬ BranchSail.branchCond op left right → AlignedPC result (pc + 4#64)))
    (fun state cfg registers _ current staged result next ran => by
      obtain ⟨direct, afterCfg, _, _, value⟩ := branch_execute_frame state cfg imm rs1 rs2 op left right
        ((registers rs1).trans read1) ((registers rs2).trans read2) result next ran
      have pcEq : state.regs.get Register.PC (cfg.init _) = pc := by
        rwa [Std.ExtDHashMap.get?_eq_some_get (cfg.init _), Option.some.injEq] at current
      exact ⟨direct, afterCfg, trivial, fun success => ⟨
        fun take => by simpa only [pcEq] using (value success).1 take,
        fun fall => ⟨((value success).2 fall).trans staged, fetched_pc_add_four_aligned fetched⟩⟩⟩) normal
  exact successor

/-- The control-flow families covered here; this classification does not redefine native support. -/
def ControlFlowInstruction : instruction → Prop
  | .JAL _ => True
  | .JALR _ => True
  | .BTYPE _ => True
  | _ => False

/-- A control-flow execute result is direct and preserves configuration and memory. This
covers successful and trapped branches without an assumption about either destination. -/
theorem control_execute_frame {decoded : instruction} (control : ControlFlowInstruction decoded)
    (state : SailState) (cfg : SailConfigured state) (result : ExecutionResult) (next : SailState)
    (executed : (runSail (execute decoded)) state = .ok result next) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ next.mem = state.mem ∧ Semantics.DestinationFrame (Semantics.instructionDestination? decoded) state next := by
  unfold ControlFlowInstruction at control
  split at control
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rd⟩⟩
    obtain ⟨direct, configured, memory, framed, _⟩ := jal_execute_frame state cfg imm rd result next executed
    exact ⟨direct, configured, memory, framed⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩⟩
    obtain ⟨value, read⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨direct, configured, memory, framed, _⟩ := jalr_execute_frame state cfg imm rs1 rd value read result next executed
    exact ⟨direct, configured, memory, framed⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs2⟩, ⟨rs1⟩, op⟩
    obtain ⟨left, read1⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, read2⟩ := initialized_gpr state cfg.init rs2
    obtain ⟨direct, configured, memory, framed, _⟩ := branch_execute_frame state cfg imm rs1 rs2 op left right read1 read2 result next executed
    exact ⟨direct, configured, memory, framed⟩
  next => contradiction

/-- Normally retiring control flow preserves the platform and every byte without a target-fetch
or target-alignment premise. This includes discarded links to x0 and the JALR low-bit mask. -/
theorem control_normal_frame {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (control : ControlFlowInstruction decoded) (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem := by
  apply normal_frame_of_direct_execute configured loaded atPc fetched decode ?_ normal
  intro state cfg result next executed
  obtain ⟨direct, afterCfg, memory, _⟩ := control_execute_frame control state cfg result next executed
  exact ⟨direct, afterCfg, memory⟩

end SP1Clean.Advance
