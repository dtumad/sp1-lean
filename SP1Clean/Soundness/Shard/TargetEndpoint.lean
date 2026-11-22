import SP1Clean.Soundness.Shard.Trace
import SP1Clean.FormalModel.Contracts.SailBoundary
import SP1Clean.FormalModel.Contracts.HostHintTarget

/-! # The trace endpoint is the complete supplied target

`Endpoint` pins the final state of an accepted trace through the trace itself and the verifier
parameters. Take the supplied target's memory as the outgoing snapshot and its host state as the
final bank. Then the Sail boundary check, agreement of the five dynamic Sail bookkeeping
registers and agreement of the host's hint suffix identify the final state with
`target.realize`.

`DynamicMatch` describes the ordinary-retirement bookkeeping. The verifier-owned
`HostHintTarget.Spec` checks the decoded suffix and the host fields preserved by the six-call
profile. The complete shard target asks for literal equality of the realized state.
-/

namespace SP1Clean.Soundness.Shard

open Circuit Air.Flat Channels Machine Semantics FormalModel.Shard
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
/-- At equal clocks the verifier authenticates the full optional Sail bookkeeping for an empty tape. -/
theorem dynamicMatch_nil_of_equal_clock {source target : ExecutionSnapshot} {header : SP1PublicIO (ZMod p)}
    (boundary : SailBoundary.Spec source target header) (clock : source.clock = target.clock) :
    DynamicMatch source target [] := by
  obtain ⟨quiet, retired⟩ := boundary.equal_clock clock
  obtain ⟨increment, interrupts, index, next⟩ := (SP1Clean.OrdinaryObservation.quiet_iff ..).mp quiet
  refine ⟨by simpa using next, by simpa using increment, ?_, by simpa using interrupts, by simpa using index⟩
  simpa using retired

omit [Fact (2 ^ 25 < p)] in
/-- The host frame and the suffix read at the authenticated head determine the whole host. -/
theorem Endpoint.host_eq {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
    {header : SP1PublicIO (ZMod p)} {events : List ExecutionEvent} {actual : ExecutionState}
    (endpoint : Endpoint source target final header events actual)
    (checked : HostHintTarget.Spec source.host target.host (Address.toNat final.head)) :
    actual.host = target.host := by
  obtain ⟨hints, decoded, host⟩ := endpoint.host
  exact host.trans (checked.outgoing_eq decoded)

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
    (endpoint : Endpoint source target final header events actual)
    (boundary : SailBoundary.Spec source target header) (dynamic : DynamicMatch source target events)
    (host : HostHintTarget.Spec source.host target.host (Address.toNat final.head)) : actual = target.realize := by
  have : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  obtain ⟨clockBound, pcBound⟩ := boundary.ranges
  have finalPc : StateMsg.pcBits (finalBoundaryStateMessage header) = target.pc :=
    SailBoundary.TargetFor.pc pcBound boundary.2.1
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
  have hostEq := endpoint.host_eq host
  have clock : actual.clock = target.clock :=
    endpoint.clock.trans (SailBoundary.TargetFor.clock clockBound boundary.2.1)
  cases actual
  simp only [ExecutionSnapshot.realize, ExecutionState.mk.injEq]
  exact ⟨sail, hostEq, clock⟩

/-- Equal authenticated clocks force an empty execution and identify the complete supplied target. -/
theorem Endpoint.empty_of_equal_clock {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
    {header : SP1PublicIO (ZMod p)} {events : List ExecutionEvent} {actual : ExecutionState}
    {policy : HostPolicy} {program : Target.GuestProgram}
    (endpoint : Endpoint source target final header events actual)
    (path : ExecutionPath policy program source.realize events actual) (boundary : SailBoundary.Spec source target header)
    (host : HostHintTarget.Spec source.host target.host (Address.toNat final.head))
    (clock : source.clock = target.clock) : events = [] ∧ actual = target.realize := by
  have : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have bound : actual.clock = target.clock :=
    endpoint.clock.trans (SailBoundary.TargetFor.clock boundary.ranges.1 boundary.2.1)
  have elapsed := path.clock
  change actual.clock = source.clock + _ at elapsed
  have := event_count_le_ticks events
  have nil : events = [] := List.length_eq_zero_iff.mp (by omega)
  subst events
  exact ⟨rfl, endpoint.realize_eq boundary (dynamicMatch_nil_of_equal_clock boundary clock) host⟩

/-- With the verifier-checked host suffix, the six-call machine trace reaches the literal supplied
Sail, host and clock state. The same ordered events bind the commitment statement. -/
theorem SailTrace.realized {commitments : CommitmentStatement} {image : ProgramImage}
    {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} {header : SP1PublicIO (ZMod p)}
    (accepted : SailTrace commitments image source target final header)
    (host : HostHintTarget.Spec source.host target.host (Address.toNat final.head)) :
    ∃ events, (sp1Machine p image).Trace source.realize events target.realize ∧
      commitments.Matches events ∧ ∀ event ∈ events, HostReceiptProfile.event true event := by
  obtain ⟨_, _, boundary, _, events, actual, path, commitmentsMatch, calls, _, _, dynamic, endpoint⟩ := accepted
  rw [endpoint.realize_eq boundary dynamic host] at path
  exact ⟨events, path, commitmentsMatch, calls⟩

end SP1Clean.Soundness.Shard
