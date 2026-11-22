module

public import SP1Clean.Semantics.Execution.ExecutionPath

/-! # The reserved HALT PC on a semantic ECALL
A continuing ECALL advances by four within the committed ROM window. A syscall whose
successor is the reserved HALT PC therefore sets the final exit status of the whole segment.
-/

@[expose] public section

namespace SP1Clean.Semantics
open Machine Soundness.Target

/-- Parking at the HALT PC authenticates a real exit by this host step. -/
theorem ExecutionStep.halt_of_parked {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {call : CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall call) target)
    (parked : call.nextPc = haltPc) : target.host.exitCode = some (call.arg1.setWidth 32) := by
  apply (step.halted_iff _).mpr
  refine ⟨call, rfl, ?_, rfl⟩
  cases step with
  | syscall success =>
    obtain ⟨pc, exec, _, fetched, _, _, _, rfl⟩ := HostState.step_observations success
    by_cases halt : exec.kind = .halt
    · simp only [HostExecution.toEvent, halt, SyscallKind.code]
    · change exec.nextPc pc = haltPc at parked
      rw [HostExecution.nextPc, ite_eq_right halt] at parked
      obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
      have addr : entry.1 = pc := by simpa using List.find?_some found
      have bound := program.rom_in_window entry (List.mem_of_find?_eq_some found)
      rw [addr] at bound
      have impossible := congrArg BitVec.toNat parked
      change (pc.toNat + 4) % 2 ^ 64 = 1 at impossible
      omega

/-- The segment begins running and retains the exit code of its parked syscall. -/
theorem ExecutionPath.halt_of_parked {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} {call : CoreSyscallEvent}
    (path : ExecutionPath policy program source events target) (member : .syscall call ∈ events)
    (parked : call.nextPc = haltPc) :
    source.host.exitCode = none ∧ target.host.exitCode = some (call.arg1.setWidth 32) := by
  induction path with
  | nil => contradiction
  | cons step tail ih =>
    refine ⟨step.running, ?_⟩
    rcases List.mem_cons.mp member with rfl | later
    · have halt := step.halt_of_parked parked
      obtain ⟨_, rfl⟩ := tail.of_halted (by rw [halt]; simp)
      exact halt
    · exact (ih later).2
end SP1Clean.Semantics
