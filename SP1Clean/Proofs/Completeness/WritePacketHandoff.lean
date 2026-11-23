import SP1Clean.Proofs.Completeness.MixedSyscallRows
import SP1Clean.Proofs.Completeness.WriteObservations
import SP1Clean.Proofs.Chips.HostControlPopulate
import SP1Clean.Proofs.Chips.WritePacket.Formal

/-! # Constructing native WRITE packet headers from mixed Sail executions -/

namespace SP1Clean.TraceGen

open Circuit Machine Semantics Soundness.Target FormalModel.Shard

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

private theorem encodeWord (value : BitVec 64) :
    wordOfNat (p := p) value.toNat = bitVecToWord value := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  apply Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (isU64_bitVecToWord _)
  rw [toBitVec64_wordOfNat, toBitVec64_bitVecToWord, BitVec.ofNat_toNat]
  rfl

/-- Every compiled ECALL produces exactly the message expected by the host constructors,
including four complete architectural words and both limbs of the incoming clock. -/
theorem syscallInstruction_hostMessage (frontier : AccessFrontier) (clock : ℕ) (pc : BitVec 64)
    (execution : HostExecution) :
    HostCallChip.message (syscallInstruction (p := p) frontier (execution.toEvent clock pc)) =
      HostControl.message clock execution := by
  unfold HostCallChip.message HostControl.message
  rw [HostCallChip.Message.mk.injEq]
  refine ⟨?_, clkLow_eq clock pc.toNat, encodeWord _, encodeWord _, encodeWord _, encodeWord _⟩
  change (cpuStateCols (p := p) clock pc.toNat).clk_high = _
  rw [cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow]

/-- At an actual WRITE, the released instruction row and the register read feeding the
native header agree with the same execution prefix. Every length and buffer word comes
from that prefix, including untouched snapshot locations. -/
theorem admissibleExecution_writePacket {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    (code : call.rawCode = SyscallKind.write.code) :
    ∃ current frontier length buffer,
      mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier) ∧
      current.sail.get_reg? 12 = some length ∧ WriteObservations.read? current.sail call = some (length, buffer) ∧
      let message := HostCallChip.message (syscallInstruction (p := SP1Prime) frontier call)
      let input := WritePacket.populate message (bitVecToWord length)
      (∀ data hint, WritePacket.circuit.ProverAssumptions input data hint) ∧
      input.call = message ∧ Address.toNat input.header.clock = call.clock ∧
      input.header.descriptor = bitVecToWord call.arg1 ∧ input.header.address = bitVecToWord call.arg2 ∧
      input.read.value = bitVecToWord length := by
  obtain ⟨current, _, frontier, length, buffer, reached, _, x12, read, _⟩ :=
    WriteObservations.of_admissibleExecution execution present code
  obtain ⟨before, incoming, next, _, same, step, _, _, _, fits, _⟩ :=
    admissibleExecution_syscall_from_prefix execution present
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (same.symm.trans reached))
  refine ⟨_, _, length, buffer, reached, x12, read, ?_⟩
  cases step with
  | syscall ran =>
    obtain ⟨pc, host, _, _, dispatched, _, _, rfl⟩ := HostState.step_observations ran
    have kind : host.kind = .write := SyscallKind.code_injective code
    have result := ((HostState.run_eq_some_iff ..).mp dispatched).2.2.2.2.1
    have small : before.clock < 2 ^ 48 := by omega
    let message := HostControl.message (p := SP1Prime) before.clock host
    have word : message.code = #v[2, 0, 0, 0] := by
      change bitVecToWord host.kind.code = _
      rw [kind]
      rfl
    have returns : message.result = message.code := by
      change bitVecToWord host.result = bitVecToWord host.kind.code
      rw [result, kind]
      rfl
    have limit := pow24_lt_sp1Prime
    have high : message.clk_high.val < 2 ^ 24 := by
      change ((before.clock / 2 ^ 24 : ℕ) : ZMod SP1Prime).val < _
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    have low : message.clk_low.val < 2 ^ 24 := by
      change ((before.clock % 2 ^ 24 : ℕ) : ZMod SP1Prime).val < _
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    rw [syscallInstruction_hostMessage]
    obtain ⟨bounded, joined, timestamp, held⟩ := WritePacket.populate_write message (bitVecToWord length) high low word returns
    exact ⟨fun _ _ => bounded, joined, timestamp.trans (HostControl.message_clock _ _ small), rfl, rfl, held⟩

end SP1Clean.TraceGen
