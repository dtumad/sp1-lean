import SP1Clean.Proofs.Completeness.MixedStateSchedule
import SP1Clean.Soundness.SyscallRowSemantics
import SP1Clean.Circuits.Gadgets.IsZero
import SP1Clean.Circuits.Gadgets.U16Compare
import SP1Clean.Circuits.Gadgets.U16toU8Safe

/-! # Compiling the instruction half of an ECALL

The native instruction observes x5, x10 and x11 in the register schedule. Its State send
uses the raw successor limbs; the separate StateBump carries those limbs when needed.
-/

namespace SP1Clean.TraceGen

open Machine Semantics Soundness.Target FormalModel.Shard

/-- One of the three scheduled register touches, in the physical C/B/A order. -/
def syscallRegisterTouch (frontier : AccessFrontier) (call : CoreSyscallEvent) (index : Fin 3) : StampedTouch :=
  let scheduled := scheduleAccessPlan frontier call.clock (syscallRegisterPlan call)
  scheduled.stampedTouches[index.val]'(by
    change index.val < 3
    exact index.isLt)

private def syscallRegisterCols {p : ℕ} (frontier : AccessFrontier) (call : CoreSyscallEvent)
    (index : Fin 3) : Circuits.Types.RegisterAccessCols (ZMod p) :=
  let touch := syscallRegisterTouch frontier call index
  registerAccessCols touch.touch.pulled.toNat touch.previous (touch.current call.clock)

/-- The active 65-column instruction row, for any of the eight successful host calls. -/
def syscallInstruction {p : ℕ} [Fact p.Prime] (frontier : AccessFrontier) (call : CoreSyscallEvent) :
    SyscallInstrsChip.Inputs (ZMod p) :=
  let id : ZMod p := call.syscallId
  let code := wordOfNat (p := p) call.rawCode.toNat
  let b := wordOfNat (p := p) call.arg1.toNat
  let c := wordOfNat (p := p) call.arg2.toNat
  let next := syscallPushedState call
  { state := cpuStateCols call.clock call.pc.toNat
    op_a := 5, op_a_memory := syscallRegisterCols frontier call 2, op_a_0 := 0
    op_b := 10, op_b_memory := syscallRegisterCols frontier call 1
    op_c := 11, op_c_memory := syscallRegisterCols frontier call 0
    next_pc := #v[(next.pc0 : ZMod p), (next.pc1 : ZMod p), (next.pc2 : ZMod p)]
    is_halt := if call.syscallId = haltSyscallId then 1 else 0
    op_a_value := wordOfNat call.result.toNat
    syscall_id_bytes := U16toU8OperationSafe.populate code
    is_enter_unconstrained := IsZeroOperation.populate (id - SyscallInstrsChip.enterUnconstrainedCode)
    is_hint_len := IsZeroOperation.populate (id - SyscallInstrsChip.hintLenCode)
    is_halt_zero := IsZeroOperation.populate (id - SyscallInstrsChip.haltCode)
    is_commit := IsZeroOperation.populate (id - SyscallInstrsChip.commitCode)
    is_commit_deferred := IsZeroOperation.populate (id - SyscallInstrsChip.commitDeferredCode)
    digest_index_bits := Vector.ofFn fun i : Fin 8 =>
      if (call.syscallId = SyscallInstrsChip.commitCode ∨ call.syscallId = SyscallInstrsChip.commitDeferredCode) ∧
          i.val = call.arg1.toNat then 1 else 0
    digest_word := if call.syscallId = SyscallInstrsChip.commitCode then
      Vector.ofFn fun i : Fin 4 => ((call.arg2.toNat / 256 ^ i.val % 256 : ℕ) : ZMod p) else 0
    op_b_cmp := ⟨if call.syscallId = SyscallInstrsChip.haltCode then
      U16CompareOperation.populate_bit b[1] SyscallInstrsChip.fieldLimbBound else 0⟩
    op_c_cmp := ⟨if call.syscallId = SyscallInstrsChip.commitDeferredCode then
      U16CompareOperation.populate_bit c[1] SyscallInstrsChip.fieldLimbBound else 0⟩
    is_real := 1 }

end SP1Clean.TraceGen
