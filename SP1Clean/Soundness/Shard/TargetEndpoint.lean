import SP1Clean.Soundness.Shard.Trace
import SP1Clean.FormalModel.Contracts.SailBoundary

/-! # The trace endpoint is the complete supplied target

`Endpoint` pins the final state of an accepted trace through the trace itself and the verifier
parameters. Take the supplied target's memory as the outgoing snapshot and its host state as the
final bank. Then the Sail boundary check, agreement of the five dynamic Sail bookkeeping
registers and agreement of the host's hint suffix identify the final state with
`target.realize`.

The two agreements are stated as equalities between the target's fields and the trace's
bookkeeping: `DynamicMatch` (C2) and `HostMatch` (C3). They are what the ordinary observation
consumer and the hint-queue terminal must establish. They are not premises of the shard target.
-/

namespace SP1Clean.Soundness.Shard

open Circuit Air.Flat Channels Machine Semantics FormalModel.Shard
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The supplied target's dynamic Sail bookkeeping agrees with the trace's: nextPC, the
retirement flag and count, the interrupt refresh and the written event index. -/
structure DynamicMatch (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop where
  nextPC : target.sail.registers.get? Register.nextPC =
    nextPcAfter events (source.sail.registers.get? Register.nextPC) (some target.pc)
  increment : target.sail.registers.get? Register.minstret_increment =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.minstret_increment
      else some (retirementEnabled source.sail.realize)
  retired : target.sail.registers.get? Register.minstret =
    (source.sail.registers.get? Register.minstret).map (fun value => value + BitVec.ofNat 64
      (if retirementEnabled source.sail.realize then events.countP ExecutionEvent.isOrdinary else 0))
  interrupts : target.sail.registers.get? Register.mip =
    if events.countP ExecutionEvent.isOrdinary = 0 then source.sail.registers.get? Register.mip
      else some (TryStepReduction.refreshedMip source.sail.realize)
  eventIndex : target.sail.registers.get? Register.written_event_index =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.written_event_index else some none

/-- The supplied target's host state is the source's, with the decoded hint suffix and the final
bank fields. -/
def HostMatch (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p)) : Prop :=
  ∀ hints, HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) =
      some hints →
    { source.host with
      io.hints := hints
      committed := target.host.committed
      deferred := target.host.deferred
      exitCode := target.host.exitCode } = target.host

omit [Fact (2 ^ 25 < p)] in
/-- A checked target stores the PC it reports. -/
private theorem pc_present {source target : ExecutionSnapshot} {header : SP1PublicIO (ZMod p)}
    (boundary : SailBoundary.Spec source target header) :
    target.sail.registers.get? Register.PC = some target.pc := by
  have present : (target.sail.registers.get? Register.PC).isSome :=
    Std.ExtDHashMap.isSome_get?_iff_mem.mpr (boundary.initialized Register.PC)
  cases stored : target.sail.registers.get? Register.PC with
  | none => simp [stored] at present
  | some value => simp [ExecutionSnapshot.pc, stored]

/-- **The final state of an accepted trace is the supplied target**, once the target's dynamic
Sail bookkeeping and host hint suffix agree with the trace. -/
theorem Endpoint.realize_eq {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
    {header : SP1PublicIO (ZMod p)} {events : List ExecutionEvent} {actual : ExecutionState}
    (endpoint : Endpoint source target.sail.memorySnapshot final target.host header events actual)
    (boundary : SailBoundary.Spec source target header) (dynamic : DynamicMatch source target events)
    (host : HostMatch source target final) : actual = target.realize := by
  have : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  obtain ⟨clockBound, pcBound⟩ := boundary.ranges
  have finalPc : StateMsg.pcBits (finalBoundaryStateMessage header) = target.pc :=
    SailBoundary.TargetFor.pc pcBound boundary.2
  have preserved (reg : Register) (frozen : SailSnapshot.executionRegister reg = false) :
      actual.sail.regs.get? reg = source.sail.registers.get? reg := by
    simp only [SailSnapshot.executionRegister, decide_eq_false_iff_not, not_or, not_exists,
      not_and] at frozen
    obtain ⟨pc, next, retired, increment, interrupts, eventIndex, gprs⟩ := frozen
    apply endpoint.preserved reg pc next retired increment interrupts eventIndex
    intro index same
    by_cases zero : index = 0
    · subst zero
      exact gprs 31#5 (by decide) (by simpa using same)
    · exact gprs index zero same
  have sail : actual.sail = target.sail.realize := by
    apply SailSnapshot.realize_eq_of_observations boundary.frame endpoint.ram endpoint.registers
    · rw [endpoint.pc, finalPc, pc_present boundary]
    · rw [endpoint.nextPC, finalPc, dynamic.nextPC]
    · rw [endpoint.retired, dynamic.retired]
    · rw [endpoint.increment, dynamic.increment]
    · rw [endpoint.interrupts, dynamic.interrupts]
    · rw [endpoint.eventIndex, dynamic.eventIndex]
    · exact preserved
    · exact endpoint.runtime
  obtain ⟨hints, decoded, hostEq⟩ := endpoint.host
  have clock : actual.clock = target.clock :=
    endpoint.clock.trans (SailBoundary.TargetFor.clock clockBound boundary.2)
  cases actual
  simp only [ExecutionSnapshot.realize, ExecutionState.mk.injEq]
  exact ⟨sail, hostEq.trans (host hints decoded), clock⟩

end SP1Clean.Soundness.Shard
