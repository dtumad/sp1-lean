module

public import SP1Clean.Semantics.Sail.SailArithmeticFrame
public import SP1Clean.Semantics.Sail.SailControlFrame
public import SP1Clean.Semantics.Sail.SailLoadFrame
public import SP1Clean.Semantics.Sail.SailStoreFrame

/-! # Supported ordinary instructions preserve the platform and protected memory

This is the circuit-independent one-step frame for the existing decoded write policy. It uses
the authoritative instruction routing projection to dispatch to arithmetic, control, load and
store proofs, without defining another supported-instruction profile.
-/

@[expose] public section

namespace SP1Clean.Advance
open LeanRV64D SP1Clean.Soundness.Target

/-- A permitted supported ordinary retirement preserves configuration and every protected byte.
The outgoing PC need not fetch unless a subsequent step executes. -/
theorem ordinary_normal_memory_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : Semantics.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      (∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address) ∧
      ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, checked⟩ := permission
  have permitted : Semantics.InstructionWrite.PermittedAt readOnly program source :=
    ⟨pc, word, decoded, atPc, fetched, decode, checked⟩
  have supported := (Semantics.InstructionWrite.check_supported readOnly source.get_reg? decoded checked).2
  have liftFrame : SailConfigured target ∧ target.mem = source.mem →
      SailConfigured target ∧ (∀ address, readOnly address = true →
        target.mem.get? address = source.mem.get? address) ∧
        ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome := by
    rintro ⟨cfg, memory⟩
    exact ⟨cfg, fun _ _ => by rw [memory], fun _ present => by simpa only [memory] using present⟩
  unfold instructionRouteId at supported
  cases routed : instructionRouteKey decoded with
  | none => simp [routed] at supported
  | some key =>
    simp only [instructionRouteKey] at routed
    split at routed
    all_goals try first
      | exact liftFrame (arithmetic_normal_frame configured loaded atPc fetched decode trivial normal)
      | exact liftFrame (control_normal_frame configured loaded atPc fetched decode trivial normal)
      | contradiction
    · rename_i imm rs1 rd unsigned width
      rcases rs1 with ⟨rs1⟩
      rcases rd with ⟨rd⟩
      exact liftFrame (load_normal_frame configured loaded atPc fetched decode normal)
    · rename_i imm rs2 rs1 width
      rcases rs2 with ⟨rs2⟩
      rcases rs1 with ⟨rs1⟩
      exact store_normal_memory_frame configured loaded atPc fetched decode permitted normal

/-- A permitted supported ordinary retirement preserves configuration and every protected byte.
The outgoing PC need not fetch unless a subsequent step executes. -/
theorem ordinary_normal_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : Semantics.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      ∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address := by
  have frame := ordinary_normal_memory_frame configured loaded permission normal
  exact ⟨frame.1, frame.2.1⟩

/-- A permitted official execute stage is direct and preserves the seven retirement registers.
Store permissions are checked on the original architectural GPRs, including through the prelude. -/
theorem permitted_execute_frame {readOnly : ℕ → Bool} {decoded : instruction} (source : SailState)
    (checked : Semantics.InstructionWrite.check readOnly source.get_reg? decoded = true)
    (state : SailState) (cfg : SailConfigured state)
    (registers : ∀ index, state.get_reg? index = source.get_reg? index)
    {result : ExecutionResult} {next : SailState}
    (executed : (runSail (LeanRV64D.Functions.execute decoded)) state = .ok result next) :
    (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ Semantics.PreservesRetirementRegisters state next := by
  have arithmetic (isArithmetic : ArithmeticInstruction decoded) :
      (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ Semantics.PreservesRetirementRegisters state next := by
    obtain ⟨actual, ran, afterCfg, _, _, held⟩ := arithmetic_execute_successor state cfg decoded isArithmetic
    rw [ran] at executed
    cases executed
    exact ⟨(fun _ h => nomatch h), afterCfg, held⟩
  have control (isControl : ControlFlowInstruction decoded) :
      (∀ other, result ≠ .ExecuteAs other) ∧ SailConfigured next ∧ Semantics.PreservesRetirementRegisters state next := by
    obtain ⟨direct, afterCfg, _, held⟩ := control_execute_frame isControl state cfg result next executed
    exact ⟨direct, afterCfg, held⟩
  have supported := (Semantics.InstructionWrite.check_supported readOnly source.get_reg? decoded checked).2
  unfold instructionRouteId at supported
  cases routed : instructionRouteKey decoded with
  | none => simp [routed] at supported
  | some key =>
    simp only [instructionRouteKey] at routed
    split at routed
    all_goals try first | exact arithmetic trivial | exact control trivial | contradiction
    · rename_i imm rs1 rd unsigned width
      rcases rs1 with ⟨rs1⟩
      rcases rd with ⟨rd⟩
      obtain ⟨direct, afterCfg, _, _, held⟩ := load_execute_successor state cfg imm rs1 rd unsigned width result next executed
      exact ⟨direct, afterCfg, held⟩
    · rename_i imm rs2 rs1 width
      rcases rs1 with ⟨rs1⟩
      rcases rs2 with ⟨rs2⟩
      have permitted : Semantics.InstructionWrite.check readOnly state.get_reg?
          (.STORE (imm, .Regidx rs2, .Regidx rs1, width)) = true := by
        rw [funext registers]
        exact checked
      obtain ⟨direct, frame⟩ := store_execute_memory_frame readOnly state cfg imm rs2 rs1 width permitted result next executed
      exact ⟨direct, frame.configured cfg, fun reg _ => congrArg (fun regs => regs.get? reg) frame.registers⟩

/-- Specialize direct execute to the successful retirement stage of the actual instruction. -/
theorem permitted_execute_preserves_retirement {readOnly : ℕ → Bool} {decoded : instruction} (source : SailState)
    (checked : Semantics.InstructionWrite.check readOnly source.get_reg? decoded = true)
    (state : SailState) (cfg : SailConfigured state)
    (registers : ∀ index, state.get_reg? index = source.get_reg? index)
    {next : SailState} (ran : (runSail (LeanRV64D.Functions.execute decoded)) state = .ok (.Retire_Success ()) next) :
    Semantics.PreservesRetirementRegisters state next :=
  (permitted_execute_frame source checked state cfg registers ran).2.2

/-- A supported normal retirement commits its staged PC and all seven dynamic bookkeeping
entries. The actual execute-stage frame follows from the decoded write permission. -/
theorem ordinary_normal_bookkeeping {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : Semantics.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    target.regs.get? Register.nextPC = target.regs.get? Register.PC ∧ Semantics.OrdinaryBookkeeping source target := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, checked⟩ := permission
  have result := normal_observed_direct_execute configured loaded atPc fetched decode
    (fun _ => True) (fun _ => True) (by
      intro state cfg registers _ _ _ outcome next executed
      obtain ⟨direct, finalCfg, _⟩ := permitted_execute_frame source checked state cfg registers executed
      exact ⟨direct, finalCfg, trivial, fun _ => trivial⟩) normal
  exact ⟨result.2.2.1, result.2.2.2.2 (fun state cfg reads _ ran =>
    permitted_execute_preserves_retirement source checked state cfg reads ran)⟩

end SP1Clean.Advance
