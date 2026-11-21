import SP1Clean.Semantics.Execution.ExecutionBoot
import SP1Clean.FormalModel.Shard
import SP1Clean.Semantics.Sail.SailControlExecute
import SP1Clean.Semantics.Sail.SailControlFrame
import SP1Clean.Proofs.Sail.InstructionDecode
import SP1Clean.Proofs.Chips.JalChip.Formal
import SP1Clean.Proofs.Chips.JalrChip.Formal
import SP1Clean.Math.SP1Field

/-! # Enabled jump links at the last instruction slot

The finite loader accepts an instruction at `2^48-4`. Official Sail boots there and normally
retires both `jal x1,0` and `jalr x1,x0,0`. Each execution satisfies the fixed capstone domain
with complete snapshots and numerical resource limits. On either native chip the enabled link addition
requires `2^48`, while the three-limb link constraint enforces a value strictly below `2^48`.
-/

namespace SP1CleanTest.Core.JumpLinkBoundary
open SP1Clean SP1Clean.Machine SP1Clean.Semantics SP1Clean.Soundness.Target LeanRV64D LeanRV64D.Functions Circuit

private def lastPc : BitVec 64 := BitVec.ofNat 64 (2 ^ 48 - 4)
private def image (word : BitVec 32) : ProgramImage := ⟨[(lastPc, word)], lastPc, []⟩

private theorem boot_retires {word : BitVec 32} {decoded : instruction}
    (valid : (image word).Valid) (parsed : InstructionDecode.decode word = some decoded)
    (run : ∀ stage, SailConfigured stage → stage.regs.get? Register.PC = some lastPc →
      stage.regs.get? Register.nextPC = some (lastPc + 4#64) → ∃ post,
      (runSail (execute decoded)) stage = .ok (.Retire_Success ()) post ∧
      SailConfigured post ∧ post.mem = stage.mem) :
    ∃ target, SailRetiresNormally (image word).initialSailState target ∧
      SailConfigured target ∧ target.mem = (image word).initialSailState.mem := by
  exact Advance.retire_frame_of_observed_execute (image word).initialSailState_configured
    ((image word).initialSailState_romLoaded valid) (image word).initialSailState_pc
    (show ((image word).toGuestProgram valid).fetchWord lastPc = some word from rfl)
    (SailDecode.instructionDecode_agrees word decoded parsed) (fun stage cfg _ => run stage cfg)

/-- The official `try_step` boots and retires `jal x1,0` at the final slot. -/
theorem jal_boot_retires : ∃ target, SailRetiresNormally (image 0x000000ef).initialSailState target ∧
    SailConfigured target ∧ target.mem = (image 0x000000ef).initialSailState.mem := by
  apply boot_retires (decoded := .JAL (0, .Regidx 1)) (by decide) rfl
  intro stage cfg pc next
  have ran := Advance.execute_JAL_reaches 0 1 lastPc stage cfg.init pc next (by decide)
  exact ⟨_, ran, Advance.SailConfigured.writeGPR (Advance.SailConfigured.writeNextPC cfg _) 1 _, rfl⟩

/-- JALR reaches the bounded aligned address zero without a successor fetch. -/
theorem jalr_boot_retires : ∃ target, SailRetiresNormally (image 0x000000e7).initialSailState target ∧
    SailConfigured target ∧ target.mem = (image 0x000000e7).initialSailState.mem := by
  apply boot_retires (decoded := .JALR (0, .Regidx 0, .Regidx 1)) (by decide) rfl
  intro stage cfg _ next
  have ran := Advance.execute_JALR_reaches 0 0 1 lastPc 0 stage cfg.init cfg.toValidMemConfig
    next (by simp [SailState.get_reg?]) (by decide)
  exact ⟨_, ran, Advance.SailConfigured.writeGPR (Advance.SailConfigured.writeNextPC cfg _) 1 _, rfl⟩

private def EncodedRun (word : BitVec 32) (valid : (image word).Valid) (policy : HostPolicy)
    (inputs : HostInputs) : Prop :=
  let program := (image word).toGuestProgram valid
  let source := (image word).executionBoot inputs
  ∃ target, ExecutionStep policy program source .ordinary ⟨target, inputs.initialHost, 9⟩ ∧
    ExecutionPath policy program source [.ordinary] ⟨target, inputs.initialHost, 9⟩ ∧
    ExecutionPath.Encoded policy program source [.ordinary]

private theorem boot_ordinary {word : BitVec 32} {decoded : instruction}
    (valid : (image word).Valid) (parsed : InstructionDecode.decode word = some decoded)
    (ordinary : word ≠ ECALL_ENC) (policy : HostPolicy) (inputs : HostInputs)
    (allowed : InstructionWrite.check policy.memory.readOnly (image word).initialSailState.get_reg? decoded = true)
    (memory : instructionMemoryEncoded (image word).initialSailState.get_reg? decoded)
    (retires : ∃ target, SailRetiresNormally (image word).initialSailState target ∧
      SailConfigured target ∧ target.mem = (image word).initialSailState.mem) :
    EncodedRun word valid policy inputs := by
  obtain ⟨target, retired, _⟩ := retires
  have atPc := (image word).initialSailState_pc
  have fetched : ((image word).toGuestProgram valid).fetchWord lastPc = some word := rfl
  have decodedAt := SailDecode.instructionDecode_agrees _ _ parsed
  have step : ExecutionStep policy ((image word).toGuestProgram valid)
      ((image word).executionBoot inputs) .ordinary ⟨target, inputs.initialHost, 9⟩ := by
    refine .ordinary rfl ?_ retired ⟨lastPc, word, decoded, atPc, fetched, decodedAt, allowed⟩
    rintro ⟨pc, atPc', fetched'⟩
    obtain rfl := Option.some.inj (atPc'.symm.trans atPc)
    exact ordinary (Option.some.inj (fetched.symm.trans fetched'))
  obtain ⟨supported, routed⟩ := InstructionWrite.check_supported _ _ _ allowed
  refine ⟨target, step, .cons step (.nil _), (ExecutionPath.encoded_cons_iff step).mpr ?_⟩
  exact ⟨⟨rfl, fun _ => ⟨lastPc, word, decoded, atPc, fetched, decodedAt, supported, routed, memory⟩⟩,
    ExecutionPath.encoded_nil⟩

/-- Any host policy and boot inputs admit the one-event encoded paths for the two enabled-link
instructions. Both start at clock one and reach clock nine. -/
theorem ordinary_from_boot (policy : HostPolicy) (inputs : HostInputs) :
    EncodedRun 0x000000ef (by decide) policy inputs ∧ EncodedRun 0x000000e7 (by decide) policy inputs :=
  ⟨boot_ordinary (decoded := .JAL (0, .Regidx 1)) (by decide) rfl (by decide) policy inputs rfl
      trivial jal_boot_retires,
   boot_ordinary (decoded := .JALR (0, .Regidx 0, .Regidx 1)) (by decide) rfl (by decide) policy inputs rfl
      trivial jalr_boot_retires⟩

private def limitsFor (demand : ResourceUsage) : ResourceLimits where
  events := demand .events
  ticks := demand .ticks
  readBytes := demand .readBytes
  writeBytes := demand .writeBytes
  allocatedHints := demand .allocatedHints
  liveHints := demand .liveHints
  liveHintBytes := demand .liveHintBytes
  requests := demand .requests
  outputBytes := demand .outputBytes
  boundaryBytes := demand .boundaryBytes
  tableRows := SP1Prime - 1
  channelOccurrences := SP1Prime - 1

private theorem fitsFor {usage demand : ResourceUsage} (within : ∀ kind, usage kind ≤ demand kind) :
    usage.Fits (limitsFor demand) := by
  intro kind
  cases kind <;> apply within

private theorem threeFit (a b c : ResourceUsage) :
    let limits := limitsFor (fun kind => a kind + b kind + c kind)
    a.Fits limits ∧ b.Fits limits ∧ c.Fits limits := by
  refine ⟨fitsFor ?_, fitsFor ?_, fitsFor ?_⟩ <;> intro kind <;> omega

private theorem snapshot_x0 (snapshot : SailSnapshot) : snapshot.memorySnapshot.Valid := by
  simp only [MemorySnapshot.Valid, SailSnapshot.memorySnapshot, Vector.getElem_ofFn]
  simp [SailState.get_reg?]

private theorem boot_valid {word : BitVec 32} (valid : (image word).Valid)
    (parsed : (image word).Decodable) (inputs : HostInputs) :
    ExecutionSourceValid (image word) ((image word).executionBootSnapshot inputs) := by
  refine ⟨⟨valid, parsed, snapshot_x0 _, (image word).initialMemory_rom valid⟩, ?_,
    (by decide : 1 < 2 ^ 48), ?_⟩
  · exact configured_with_memory (cfgState_configured lastPc) _
  · change (((image word).initialSailState.regs.get? Register.PC).getD 0).toNat < 2 ^ 48
    rw [(image word).initialSailState_pc]
    exact (by decide : lastPc.toNat < 2 ^ 48)

/-- Supply complete source and target snapshots and finite data-only limits. The target captures
all actual Sail runtime fields using the unchanged sparse boot memory. -/
private theorem admissible_of_run {word : BitVec 32} (valid : (image word).Valid)
    (parsed : (image word).Decodable) (inputs : HostInputs) (next : BitVec 64)
    (bound : next.toNat < NativeLayout.guestMemory.upper)
    (run : EncodedRun word valid (FormalModel.Shard.policy SP1Prime (image word)) inputs)
    (readout : ∀ target, SailRetiresNormally (image word).initialSailState target →
      target.regs.get? Register.PC = some next ∧ target.mem = (image word).initialSailState.mem) :
    ∃ limits target, FormalModel.Shard.AdmissibleExecution limits SP1Prime (image word)
      ((image word).executionBootSnapshot inputs) target [.ordinary] := by
  let policy := FormalModel.Shard.policy SP1Prime (image word)
  let image' := image word
  let source := image'.executionBootSnapshot inputs
  obtain ⟨terminal, step, path, encoded⟩ := run
  have normal : SailRetiresNormally image'.initialSailState terminal := by cases step; assumption
  obtain ⟨pc, memory⟩ := readout terminal normal
  let targetState : ExecutionState := ⟨terminal, inputs.initialHost, 9⟩
  let target := ExecutionSnapshot.capture targetState image'.initialMemory
  have same : target.realize = targetState := ExecutionSnapshot.realize_capture _ _ memory.symm
  let usage := executionResources policy image'.program source.realize [.ordinary]
  let limits := limitsFor (fun kind => usage kind + source.realize.resources kind + target.realize.resources kind)
  have fits := threeFit usage source.realize.resources target.realize.resources
  refine ⟨limits, target, ⟨boot_valid valid parsed inputs, ?_⟩, ?_, fits.1, fits.2.1, fits.2.2,
    (by decide : 9 < NativeLayout.clocks.upper), ?_⟩
  · rw [same, ProgramImage.executionBootSnapshot_realize, ProgramImage.program_eq _ valid]
    exact path
  · rw [ProgramImage.executionBootSnapshot_realize, ProgramImage.program_eq _ valid]
    exact encoded
  · change ((terminal.regs.get? Register.PC).getD 0).toNat < NativeLayout.guestMemory.upper
    simpa only [pc, Option.getD_some] using bound

/-- Both concrete programs satisfy the complete fixed capstone domain at the SP1 field
characteristic, for some numerical limits and a complete reached target snapshot. -/
theorem admissible_from_boot (inputs : HostInputs) :
    (∃ limits target, FormalModel.Shard.AdmissibleExecution limits SP1Prime (image 0x000000ef)
      ((image 0x000000ef).executionBootSnapshot inputs) target [.ordinary]) ∧
    (∃ limits target, FormalModel.Shard.AdmissibleExecution limits SP1Prime (image 0x000000e7)
      ((image 0x000000e7).executionBootSnapshot inputs) target [.ordinary]) := by
  constructor
  · let rom := image 0x000000ef
    have valid : rom.Valid := by decide
    apply admissible_of_run valid (by decide) inputs lastPc (by decide)
      ((ordinary_from_boot (FormalModel.Shard.policy SP1Prime rom) inputs).1)
    intro target normal
    have decoded := SailDecode.instructionDecode_agrees 0x000000ef (.JAL (0, .Regidx 1)) rfl
    have fetched : (rom.toGuestProgram valid).fetchWord lastPc = some 0x000000ef := rfl
    exact ⟨Advance.jal_normal_successor rom.initialSailState_configured
      (rom.initialSailState_romLoaded valid) rom.initialSailState_pc fetched decoded normal,
      (Advance.control_normal_frame rom.initialSailState_configured (rom.initialSailState_romLoaded valid)
        rom.initialSailState_pc fetched decoded trivial normal).2⟩
  · let rom := image 0x000000e7
    have valid : rom.Valid := by decide
    apply admissible_of_run valid (by decide) inputs 0 (by decide)
      ((ordinary_from_boot (FormalModel.Shard.policy SP1Prime rom) inputs).2)
    intro target normal
    have decoded := SailDecode.instructionDecode_agrees 0x000000e7 (.JALR (0, .Regidx 0, .Regidx 1)) rfl
    have fetched : (rom.toGuestProgram valid).fetchWord lastPc = some 0x000000e7 := rfl
    exact ⟨Advance.jalr_normal_successor (value := 0) rom.initialSailState_configured
      (rom.initialSailState_romLoaded valid) rom.initialSailState_pc fetched
      (by simp [SailState.get_reg?]) decoded normal,
      (Advance.control_normal_frame rom.initialSailState_configured (rom.initialSailState_romLoaded valid)
        rom.initialSailState_pc fetched decoded trivial normal).2⟩

private theorem link_impossible {pc link : Word (ZMod SP1Prime)}
    (last : pc.toBitVec64 = lastPc) (bounded : link.isU64) (top : link[3] = 0)
    (value : link.toBitVec64 = pc.toBitVec64 + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod SP1Prime))) : False := by
  rw [last, show Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod SP1Prime)) = 4#64 from by decide] at value
  have full : link.toNat = 2 ^ 48 := (Word.toBitVec64_toNat bounded).symm.trans (congrArg BitVec.toNat value)
  rw [Word.toNat_def, top, ZMod.val_zero] at full
  obtain ⟨h0, h1, h2, _⟩ := Word.lt_cases_of_isU64 bounded
  omega

private def EnabledLast (pc : Vector (ZMod SP1Prime) 3) (active zero : ZMod SP1Prime) : Prop :=
  let word : Word (ZMod SP1Prime) := #v[pc[0], pc[1], pc[2], 0]
  active = 1 ∧ zero = 0 ∧ word.isU64 ∧ word.toBitVec64 = lastPc

/-- The exact three physical PC limbs at the final slot meet the row-impossibility premises. -/
theorem last_slot_encoding : EnabledLast #v[65532, 65535, 65535] 1 0 := by
  refine ⟨rfl, rfl, Word.isU64_of_cases ?_ ?_ ?_ ?_, ?_⟩ <;> decide

open SP1Clean.JalChip in
/-- No assignment to the real JAL row with an enabled destination at the last slot satisfies
its constraints and lookup requirements. The witnessed link word is arbitrary. -/
theorem jal_row_impossible : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalChip.main
    (fun input _ => EnabledLast input.state.pc input.is_real input.adapter.op_a_0)
    (fun _ _ _ => False) := by
  circuit_proof_start
  obtain ⟨real, zero, pcBound, last⟩ := h_assumptions
  obtain ⟨_, _, _, linkAdd, top, _⟩ := h_holds
  have gate : input_is_real - input_adapter_op_a_0 = 1 := by rw [real, zero, sub_zero]
  obtain ⟨bound, value⟩ := linkAdd ⟨fun _ => ⟨pcBound, Word.isU64_four⟩, Or.inr gate⟩ gate
  exact (link_impossible last bound top value).elim

open SP1Clean.JalrChip in
/-- The JALR link uses the same active gate and high-limb constraint, independently of rs1, the
immediate and the chosen jump address. -/
theorem jalr_row_impossible : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalrChip.main
    (fun input _ => EnabledLast input.state.pc input.is_real input.adapter.op_a_0)
    (fun _ _ _ => False) := by
  circuit_proof_start
  obtain ⟨real, zero, pcBound, last⟩ := h_assumptions
  obtain ⟨_, _, _, _, linkAdd, top, _⟩ := h_holds
  have gate : input_is_real - input_adapter_op_a_0 = 1 := by rw [real, zero, sub_zero]
  obtain ⟨bound, value⟩ := linkAdd ⟨fun _ => ⟨pcBound, Word.isU64_four⟩, Or.inr gate⟩ gate
  exact (link_impossible last bound top value).elim

end SP1CleanTest.Core.JumpLinkBoundary
