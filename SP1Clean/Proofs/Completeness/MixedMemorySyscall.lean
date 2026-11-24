import SP1Clean.Proofs.Completeness.MixedMemoryPosts
import SP1Clean.Proofs.Completeness.MixedSyscallCoordinates
import SP1Clean.Soundness.SystemTouches

/-! # Exact Memory transfers of the generated ECALL instruction

The instruction reads its compressed register timestamps from the actual populated columns.
The scheduler supplies a refresh whenever required, so these records have the same complete
prior timestamps as their stamped source operands. The three pushed words likewise come
from the original ECALL row, including the true result of the write to x5.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Circuit Channels Semantics Soundness Machine FormalModel.Shard

private abbrev F := ZMod SP1Prime

private theorem regLimbs (index : BitVec 5) :
    index.toNat % 2 ^ 16 = index.toNat ∧ index.toNat / 2 ^ 16 % 2 ^ 16 = 0 ∧
      index.toNat / 2 ^ 32 % 2 ^ 16 = 0 := by
  have := index.isLt
  omega

/-- The prior word read from a populated register block has the complete original timestamp.
This works on every scheduled register operand, including repeated uses within one row. -/
theorem register_pull {frontier : AccessFrontier} {base : ℕ} {plan : InstructionAccessPlan}
    {touch : StampedTouch} (member : touch ∈ (scheduleAccessPlan frontier base plan).stampedTouches)
    (phase : activeClockPhase base) {i : BitVec 5} (loc : touch.touch.loc = .reg i)
    (role : touch.touch.slot ≠ .ram) (pc : ℕ) :
    let block := registerAccessCols (p := SP1Prime) touch.touch.pulled.toNat touch.previous (touch.current base)
    let state := cpuStateCols (p := SP1Prime) base pc
    SystemTouches.prior state block (i.toNat : F) =
      (MemoryHistoryAccess.ofStamped base touch).pulledEntry.toMemoryMsg := by
  obtain ⟨before, after⟩ := scheduleAccessPlan_register_window phase.window member loc role
  change touch.previous / 2 ^ 24 = base / 2 ^ 24 at before
  change touch.current base / 2 ^ 24 = base / 2 ^ 24 at after
  obtain ⟨low, mid, high⟩ := regLimbs i
  dsimp only
  simp only [SystemTouches.prior, cpuStateCols_clk_high, registerAccessCols_prev_low, registerAccessCols_prev_value,
    prevLowOf, Nat.shiftRight_eq_div_pow, before.trans after.symm, ↓reduceIte,
    MemRecordEntry.toMemoryMsg, MemoryHistoryAccess.pulledEntry, MemoryHistoryAccess.ofStamped,
    loc, MemLoc.busAddress, low, mid, high, Nat.cast_zero, after]

/-- The pushed timestamp at a register role has the original CPU high limb and its role offset.
The posted word is the word the corresponding semantic touch writes. -/
theorem register_push (base pc : ℕ) (phase : activeClockPhase base) (touch : StampedTouch)
    {i : BitVec 5} (loc : touch.touch.loc = .reg i) :
    let state := cpuStateCols (p := SP1Prime) base pc
    SystemTouches.push state (i.toNat : F) (touch.touch.slot.recordOffset : F) (wordOfNat touch.touch.pushed.toNat) =
      (MemoryHistoryAccess.ofStamped base touch).pushedEntry.toMemoryMsg := by
  have window := phase.window
  change base % 2 ^ 24 + 4 < 2 ^ 24 at window
  have bound := touch.touch.slot.recordOffset_le_four
  have highTime : touch.current base / 2 ^ 24 = base / 2 ^ 24 := by
    change (base + touch.touch.slot.recordOffset) / 2 ^ 24 = _
    omega
  have lowTime : touch.current base % 2 ^ 24 = base % 2 ^ 24 + touch.touch.slot.recordOffset := by
    change (base + touch.touch.slot.recordOffset) % 2 ^ 24 = _
    omega
  obtain ⟨low, mid, high⟩ := regLimbs i
  dsimp only
  simp only [SystemTouches.push, cpuStateCols_clk_high, clkLow_eq, Nat.shiftRight_eq_div_pow,
    MemoryHistoryAccess.pushedEntry, MemoryHistoryAccess.ofStamped, MemRecordEntry.toMemoryMsg,
    loc, MemLoc.busAddress, low, mid, high, Nat.cast_zero, highTime, lowTime, Nat.cast_add]

/-- Every pulled register record on the original generated ECALL row is the corresponding
canonical semantic predecessor. The physical A/B/C order reverses the C/B/A schedule. -/
theorem syscall_pulls (frontier : AccessFrontier) (call : CoreSyscallEvent) (phase : activeClockPhase call.clock) :
    let row := syscallInstruction (p := SP1Prime) frontier call
    ((syscallRowFacts row).memPulls.map Prod.fst) =
      ((instruction (.syscall frontier call.clock call)).map (fun a => a.pulledEntry.toMemoryMsg)).reverse := by
  let touch := syscallRegisterTouch frontier call
  have pull (j : Fin 3) {i : BitVec 5} (loc : (touch j).touch.loc = .reg i) (role : (touch j).touch.slot ≠ .ram) :=
    register_pull (frontier := frontier) (plan := syscallRegisterPlan call) (touch := touch j) (List.getElem_mem ..) phase loc role call.pc.toNat
  exact congrArg₂ List.cons (pull 2 (i := 5) rfl (by change AccessSlot.opA ≠ .ram; decide)) (congrArg₂ List.cons (pull 1 (i := 10) rfl (by change AccessSlot.opB ≠ .ram; decide))
    (congrArg (· :: []) (pull 0 (i := 11) rfl (by change AccessSlot.opC ≠ .ram; decide))))

/-- The original pushed records of ECALL are exactly the generated register posts,
including the updated x5 and both readbacks. -/
theorem syscall_posts (frontier : AccessFrontier) (call : CoreSyscallEvent) (phase : activeClockPhase call.clock) :
    let row := syscallInstruction (p := SP1Prime) frontier call
    (syscallRowFacts row).memPushes =
      ((instruction (.syscall frontier call.clock call)).map (fun a => a.pushedEntry.toMemoryMsg)).reverse := by
  let touch := syscallRegisterTouch frontier call
  have push (j : Fin 3) {i : BitVec 5} (loc : (touch j).touch.loc = .reg i) := register_push call.clock call.pc.toNat phase (touch j) loc
  exact congrArg₂ List.cons (push 2 (i := 5) rfl) (congrArg₂ List.cons (push 1 (i := 10) rfl)
    (congrArg (· :: []) (push 0 (i := 11) rfl)))

end SP1Clean.TraceGen.MixedMemoryHistory
