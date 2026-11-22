import SP1Clean.Proofs.Completeness.MixedSyscallInstruction

/-! # Architectural and physical coordinates of a compiled ECALL -/

namespace SP1Clean.TraceGen

open Machine Semantics Soundness.Target FormalModel.Shard
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact p.Prime] in
private theorem clock_decode (clk pc : ℕ) (fits : clk < 2 ^ 48) :
    let cpu := cpuStateCols (p := p) clk pc
    cpu.clk_high.val * 2 ^ 24 + cpu.clk_16_24.val * 2 ^ 16 + cpu.clk_0_16.val = clk := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  dsimp only
  rw [cpuStateCols_clk_high, cpuStateCols_clk_16_24, cpuStateCols_clk_0_16,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  repeat rw [ZMod.val_natCast_of_lt (by omega)]
  omega

omit [Fact p.Prime] in
private theorem pc_decode (clk : ℕ) (pc : BitVec 64) (fits : pc.toNat < 2 ^ 48) :
    let cpu := cpuStateCols (p := p) clk pc.toNat
    (BitVec.ofNat 64 (cpu.pc[0].val + cpu.pc[1].val * 2 ^ 16 + cpu.pc[2].val * 2 ^ 32)) = pc := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  dsimp only
  rw [cpuStateCols_pc_zero, cpuStateCols_pc_one, cpuStateCols_pc_two,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  repeat rw [ZMod.val_natCast_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

private theorem nextPc_decode (call : CoreSyscallEvent) (law : call.PcLaw) (fits : call.pc.toNat < 2 ^ 48) :
    let next := syscallPushedState call
    BitVec.ofNat 64 (((next.pc0 : ZMod p).val) + ((next.pc1 : ZMod p).val) * 2 ^ 16 +
      ((next.pc2 : ZMod p).val) * 2 ^ 32) = call.nextPc := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  unfold CoreSyscallEvent.PcLaw at law
  by_cases h : call.syscallId = haltSyscallId
  · rw [ite_eq_left h] at law
    rw [law]
    simp only [syscallPushedState, ite_eq_left h, StateRecord.selected, StateRecord.canonical,
      show haltPc.toNat = 1 from rfl]
    have : Fact (1 < p) := ⟨by omega⟩
    norm_num [ZMod.val_one, haltPc]
  · rw [ite_eq_right h] at law
    rw [law]
    simp only [syscallPushedState, ite_eq_right h, StateRecord.fallThrough, StateRecord.canonical]
    repeat rw [ZMod.val_natCast_of_lt (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    change _ = (call.pc.toNat + 4) % 2 ^ 64
    omega

/-- Decoding every architectural field of the compiled row recovers the original event.
The uncarried ECALL successor decodes correctly at a low-limb crossing. -/
theorem syscallEventOfRow_syscallInstruction (frontier : AccessFrontier) (call : CoreSyscallEvent)
    (law : call.PcLaw) (clock : call.clock < 2 ^ 48) (pc : call.pc.toNat < 2 ^ 48) :
    Soundness.syscallEventOfRow (syscallInstruction (p := p) frontier call) = call := by
  change CoreSyscallEvent.mk _ _ _ _ _ _ _ =
    CoreSyscallEvent.mk call.clock call.pc call.nextPc call.rawCode call.arg1 call.arg2 call.result
  congr 1
  · exact clock_decode (p := p) call.clock call.pc.toNat clock
  · exact pc_decode (p := p) call.clock call.pc pc
  · exact nextPc_decode (p := p) call law pc
  all_goals
    apply (toBitVec64_wordOfNat (p := p) _).trans
    exact (BitVec.ofNat_toNat 64 _).trans (by rfl)

/-- Register values, addresses and bounded limbs required by the native receiver. -/
theorem syscallInstruction_pulledFacts (frontier : AccessFrontier) (call : CoreSyscallEvent) :
    SyscallInstrsChip.PulledFacts (syscallInstruction (p := p) frontier call) := by
  intro _
  have hp := Fact.out (p := 2 ^ 25 < p)
  obtain ⟨low, middle, high⟩ := cpuStateCols_pc_val_lt (p := p) call.clock call.pc.toNat
  exact ⟨by change (5 : ZMod p).val < 32; rw [show (5 : ZMod p).val = 5 from
                ZMod.val_natCast_of_lt (by omega : 5 < p)]; decide,
    low, middle, high, Or.inl rfl, wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt ..,
    wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt ..,
    wordOfNat_isU64 _, registerAccessCols_prevLow_val_lt .., wordOfNat_isU64 _⟩

/-- At an actual cut, all three register readers use the preceding timestamp selected by
the canonical scheduler, including its refresh when the preceding use was in an older window. -/
theorem syscallInstruction_readers (frontier : AccessFrontier) (call : CoreSyscallEvent)
    (phase : activeClockPhase call.clock)
    (ordered : ∀ touch ∈ (scheduleAccessPlan frontier call.clock (syscallRegisterPlan call)).stampedTouches,
      touch.previous < touch.current call.clock) :
    let r := syscallInstruction (p := p) frontier call
    Readers.CPUState.Spec ⟨r.state, r.next_pc, 264, r.is_real⟩ ∧
    Readers.RegisterAccessCols.Spec ⟨r.op_a_memory, r.is_real, SyscallInstrsChip.clkLow r + 4⟩ ∧
    Readers.RegisterAccessCols.Spec ⟨r.op_b_memory, r.is_real, SyscallInstrsChip.clkLow r + 3⟩ ∧
    Readers.RegisterAccessCols.Spec ⟨r.op_c_memory, r.is_real, SyscallInstrsChip.clkLow r + 2⟩ := by
  have earlier (i : Fin 3) := ordered (syscallRegisterTouch frontier call i) (List.getElem_mem ..)
  exact ⟨cpuState_spec _ _ phase _ _ _, registerAccessCols_spec_opA phase (earlier 2),
    registerAccessCols_spec_opB phase (earlier 1), registerAccessCols_spec_opC phase (earlier 0)⟩

/-- Physical PC carry behavior for both the parking and continuing branches. -/
theorem syscallInstruction_pcArm (frontier : AccessFrontier) (call : CoreSyscallEvent) :
    let r := SyscallInstrsChip.toPcArm (syscallInstruction (p := p) frontier call)
    SyscallInstrsChip.PcArm.Assumptions r ∧ SyscallInstrsChip.PcArm.Spec r := by
  let r := SyscallInstrsChip.toPcArm (syscallInstruction (p := p) frontier call)
  have gate : r.is_halt = if call.syscallId = haltSyscallId then 1 else 0 := rfl
  by_cases halt : call.syscallId = haltSyscallId
  · rw [ite_eq_left halt] at gate
    refine ⟨⟨Or.inr rfl, Or.inr gate⟩, fun _ => ?_, fun _ impossible => (one_ne_zero (gate.symm.trans impossible)).elim⟩
    change (syscallPushedState call).pc0.cast = (1 : ZMod p) ∧
      (syscallPushedState call).pc1.cast = (0 : ZMod p) ∧ (syscallPushedState call).pc2.cast = (0 : ZMod p)
    simp [syscallPushedState, halt, StateRecord.selected, StateRecord.canonical, haltPc]
  · rw [ite_eq_right halt] at gate
    refine ⟨⟨Or.inr rfl, Or.inl gate⟩, fun impossible => (zero_ne_one (gate.symm.trans impossible)).elim, fun _ _ => ?_⟩
    change ((syscallPushedState call).pc0 : ZMod p) = _ ∧ ((syscallPushedState call).pc1 : ZMod p) = _ ∧
      ((syscallPushedState call).pc2 : ZMod p) = _
    simp only [syscallPushedState, ite_eq_right halt, StateRecord.fallThrough, StateRecord.canonical, Nat.cast_add]
    change _ = (cpuStateCols (p := p) call.clock call.pc.toNat).pc[0] + 4 ∧ _ = (cpuStateCols (p := p) call.clock call.pc.toNat).pc[1] ∧
      _ = (cpuStateCols (p := p) call.clock call.pc.toNat).pc[2]
    simp only [cpuStateCols_pc_zero, cpuStateCols_pc_one, cpuStateCols_pc_two, Nat.shiftRight_eq_div_pow,
      Nat.cast_ofNat, and_self]

omit [Fact (2 ^ 25 < p)] in
/-- The two State interactions have the actual five physical fields, including unnormalized carries. -/
theorem syscallInstruction_stateMessages (frontier : AccessFrontier) (call : CoreSyscallEvent) :
    let r := syscallInstruction (p := p) frontier call
    Soundness.SyscallInstrsChip.statePulledMessage r = (StateRecord.canonical call.clock call.pc.toNat).toMessage ∧
    Soundness.SyscallInstrsChip.statePushedMessage r = (syscallPushedState call).toMessage := by
  let cpu := cpuStateCols (p := p) call.clock call.pc.toNat
  have high : cpu.clk_high = (call.clock / 2 ^ 24 : ℕ) := by
    rw [show cpu.clk_high = _ from cpuStateCols_clk_high .., Nat.shiftRight_eq_div_pow]
  have low : cpu.clk_0_16 + cpu.clk_16_24 * 65536 = (call.clock % 2 ^ 24 : ℕ) := clkLow_eq ..
  constructor
  · change Channels.StateMsg.mk cpu.clk_high (cpu.clk_0_16 + cpu.clk_16_24 * 65536) cpu.pc[0] cpu.pc[1] cpu.pc[2] = _
    rw [high, low]
    simp only [cpu, StateRecord.toMessage, StateRecord.canonical, cpuStateCols_pc_zero, cpuStateCols_pc_one,
      cpuStateCols_pc_two, Nat.shiftRight_eq_div_pow]
  · let raw := syscallPushedState call
    change Channels.StateMsg.mk cpu.clk_high (cpu.clk_0_16 + cpu.clk_16_24 * 65536 + 264) raw.pc0 raw.pc1 raw.pc2 = _
    rw [high, low]
    suffices (syscallPushedState call).clkHigh = call.clock / 2 ^ 24 ∧
      (syscallPushedState call).clkLow = call.clock % 2 ^ 24 + 264 by
      simp only [raw, StateRecord.toMessage, this.1, this.2, Nat.cast_add, Nat.cast_ofNat]
    unfold syscallPushedState
    split <;> exact ⟨rfl, rfl⟩

end SP1Clean.TraceGen
