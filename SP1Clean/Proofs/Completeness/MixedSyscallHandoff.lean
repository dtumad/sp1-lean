import SP1Clean.Proofs.Completeness.MixedSyscallCoordinates
import SP1Clean.Proofs.Chips.HostControlPopulate

/-! # The released instruction-to-host message of every populated ECALL -/

namespace SP1Clean.TraceGen
open Circuit Machine Semantics Soundness.Target

variable {p : Nat} [Fact p.Prime] [Fact (2^25 < p)]

private theorem encodeWord (value : BitVec 64) :
    wordOfNat (p := p) value.toNat = bitVecToWord value := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  apply Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (isU64_bitVecToWord _)
  rw [toBitVec64_wordOfNat, toBitVec64_bitVecToWord, BitVec.ofNat_toNat]
  rfl

/-- Time, full code, register inputs and x5 result taken directly from a mixed tape event. -/
def eventHostMessage (call : CoreSyscallEvent) : HostCallChip.Message (ZMod p) :=
  ⟨(call.clock / 2^24 : Nat), (call.clock % 2^24 : Nat), bitVecToWord call.rawCode,
    bitVecToWord call.arg1, bitVecToWord call.arg2, bitVecToWord call.result⟩

/-- Reading the full host handoff from any populated instruction yields its exact tape payload,
independently of the predecessor timestamps in its register columns. -/
theorem syscallInstruction_eventMessage (frontier : AccessFrontier) (call : CoreSyscallEvent) :
    HostCallChip.message (syscallInstruction (p := p) frontier call) = eventHostMessage call := by
  unfold HostCallChip.message eventHostMessage
  rw [HostCallChip.Message.mk.injEq]
  refine ⟨?_, clkLow_eq call.clock call.pc.toNat, encodeWord _, encodeWord _, encodeWord _, encodeWord _⟩
  change (cpuStateCols (p := p) call.clock call.pc.toNat).clk_high = _
  rw [cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow]

/-- Every compiled ECALL produces exactly the message expected by the host constructors,
including four complete architectural words and both limbs of the incoming clock. -/
theorem syscallInstruction_hostMessage (frontier : AccessFrontier) (clock : ℕ) (pc : BitVec 64)
    (execution : HostExecution) :
    HostCallChip.message (syscallInstruction (p := p) frontier (execution.toEvent clock pc)) =
      HostControl.message clock execution :=
  syscallInstruction_eventMessage frontier _

end SP1Clean.TraceGen
