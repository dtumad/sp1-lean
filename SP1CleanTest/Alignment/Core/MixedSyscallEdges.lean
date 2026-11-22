import SP1Clean.Proofs.Completeness.MixedSyscallCoordinates
import SP1Clean.Math.SP1Field

/-! # A continuing ECALL at simultaneous PC and timestamp crossings -/

namespace SP1CleanTest.Alignment.MixedSyscallEdges

open SP1Clean SP1Clean.Machine SP1Clean.Semantics SP1Clean.TraceGen

-- x5 was used earlier in the current window. x10 and x11 were last used at boot.
private def prior : AccessFrontier := Function.update AccessFrontier.initial (.reg 5) (2 ^ 24 + 7)

private def call : CoreSyscallEvent :=
  ⟨2 * 2 ^ 24 - 7, BitVec.ofNat 64 (2 ^ 32 - 4), BitVec.ofNat 64 (2 ^ 32),
    SyscallKind.verifyProof.code, 10, 11, SyscallKind.verifyProof.code⟩

private def row := syscallInstruction (p := SP1Prime) prior call

-- The row posts the uncarried low limb. The following StateBump carries through the middle limb.
example : row.next_pc = #v[65536, 65535, 0] := by decide
example : (syscallPushedState call).normalize = StateRecord.canonical (2 * 2 ^ 24 + 257) (2 ^ 32) := by decide

-- The two cross-window operands are refreshed in C/B order and read those exact new timestamps.
example : ((scheduleAccessPlan prior call.clock (syscallRegisterPlan call)).memoryBumps.map (·.addr)) = [11, 10] := by decide
example : (row.op_c_memory.access_timestamp.prev_low.val, row.op_b_memory.access_timestamp.prev_low.val,
    row.op_a_memory.access_timestamp.prev_low.val) = (2 ^ 24 - 6, 2 ^ 24 - 6, 7) := by decide

example : SP1Clean.Soundness.syscallEventOfRow row = call :=
  syscallEventOfRow_syscallInstruction prior call (by unfold CoreSyscallEvent.PcLaw; decide) (by decide) (by decide)

end SP1CleanTest.Alignment.MixedSyscallEdges
