import SP1Clean

/-! # Mixed read-time regression

The Memory transport must accept syscall rows without imposing the ordinary carrier's
all-reads-at-start restriction. This kernel-checked regression distinguishes those two interfaces.
-/

namespace SP1Clean.Audit.MixedMemoryRows

open SP1Clean.Soundness SP1Clean.Semantics SP1Clean.Soundness.NativeCore

variable {p : ℕ} [Fact p.Prime]

/-- The ledger interface admits the syscall carrier, whereas the ordinary alignment interface
cannot accept its later register reads as the original carrier. -/
theorem syscallKeepsMixedReadTimes (row : SyscallInstrsChip.Inputs (ZMod p)) :
    RowMemoryPermutation (syscallRowFacts row) (syscallRowFacts row) ∧
      ¬ ∃ aligned, TimedGrounding.AlignsWith aligned (syscallRowFacts row) := by
  refine ⟨RowMemoryPermutation.refl _, ?_⟩
  rintro ⟨aligned, agreement⟩
  have late := agreement.ordTime
    (SyscallInstrsChip.memPulledMessage row row.op_b_memory row.op_b,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 3)
    (by simp [syscallRowFacts])
  change StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 3 =
    StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) at late
  omega

end SP1Clean.Audit.MixedMemoryRows
