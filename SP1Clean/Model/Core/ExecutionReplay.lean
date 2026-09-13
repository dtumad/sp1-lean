import SP1Clean.Model.Core.ExecutionPath
import SP1Clean.Model.Machine.Execution

/-! # Replaying mixed event tapes with evolving host state

Replay consumes only the source state and event data. A host event is checked against the call
computed from the actual registers, memory, host queue, and clock; its claimed result is not used
as an oracle. The returned host state feeds the next step. Ordinary replay uses official Sail.

`ExecutionStep.replay` and `ExecutionPath.replay` establish agreement with the semantic relation.
The converse still requires normal-retirement evidence for ordinary instructions: successful
`try_step` evaluation alone also includes interpreter paths other than instruction retirement.
This semantic Sail replay is noncomputable, like the existing machine replay; it is not the
exportable row compiler. Its prefix trajectory supplies the paired state for mixed grounding.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D

/-- Computable host replay checks the whole event against the concrete interpreter result. -/
def replayHost? (policy : HostPolicy) (program : GuestProgram) (source : ExecutionState)
    (event : CoreSyscallEvent) : Option ExecutionState := do
  let (host, sail, actual) ← source.host.step policy program source.clock source.sail
  if actual = event then some ⟨sail, host, source.clock + syscallSchedule.duration⟩ else none

theorem replayHost?_eq_some_iff (policy : HostPolicy) (program : GuestProgram)
    (source target : ExecutionState) (event : CoreSyscallEvent) :
    replayHost? policy program source event = some target ↔
      ExecutionStep policy program source (.syscall event) target := by
  constructor
  · intro success
    simp only [replayHost?, bind, Option.bind_eq_some_iff] at success
    obtain ⟨⟨host, sail, actual⟩, ran, success⟩ := success
    dsimp only at success
    split_ifs at success with same
    · subst actual
      cases success
      exact .syscall ran
  · intro step
    cases step with
    | syscall ran => simp [replayHost?, ran]

/-- The Boolean ECALL test observes the actual PC in the committed program. -/
def ExecutionState.atEcall (program : GuestProgram) (source : ExecutionState) : Bool :=
  ((source.sail.regs.get? LeanRV64D.Defs.Register.PC).bind program.fetchWord) == some ECALL_ENC

theorem ExecutionState.atEcall_iff (program : GuestProgram) (source : ExecutionState) :
    source.atEcall program = true ↔ AboutToExecuteEcall program source.sail := by
  simp [ExecutionState.atEcall, AboutToExecuteEcall, Option.bind_eq_some_iff]

/-- Replay one label, guarding both arms against resumption after HALT. -/
noncomputable def replayStep? (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) : ExecutionEvent → Option ExecutionState
  | .ordinary =>
      if source.host.exitCode.isSome || source.atEcall program then none
      else (stepOnce source.sail).map fun sail =>
        ⟨sail, source.host, source.clock + ordinarySchedule.duration⟩
  | .syscall event => replayHost? policy program source event

/-- Every semantic transition is reconstructed from its event label and incoming whole state. -/
theorem ExecutionStep.replay {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target) :
    replayStep? policy program source event = some target := by
  cases step with
  | ordinary running notEcall normal =>
      have notAtEcall : source.atEcall program = false :=
        Bool.eq_false_iff.mpr (fun atEcall => notEcall ((source.atEcall_iff program).mp atEcall))
      obtain ⟨_, stepped⟩ := normal.sailStep
      simp [replayStep?, running, notAtEcall, stepOnce, stepped]
  | syscall ran => exact (replayHost?_eq_some_iff _ _ _ _ _).mpr (.syscall ran)

/-- A source plus an event tape determines every intermediate host and Sail state. -/
noncomputable def replayEvents? (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → Option ExecutionState
  | source, [] => some source
  | source, event :: rest =>
      (replayStep? policy program source event).bind fun next => replayEvents? policy program next rest

/-- Replay itself composes at a semantic cut; no proof term or initial-state reset is involved. -/
theorem replayEvents?_append (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (first second : List ExecutionEvent) :
    replayEvents? policy program source (first ++ second) =
      (replayEvents? policy program source first).bind fun middle =>
        replayEvents? policy program middle second := by
  induction first generalizing source with
  | nil => rfl
  | cons event rest ih => simp only [List.cons_append, replayEvents?, ih, Option.bind_assoc]

theorem ExecutionPath.replay {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    replayEvents? policy program source events = some target := by
  induction path with
  | nil => rfl
  | cons step _ ih => simp only [replayEvents?, step.replay, Option.bind_some, ih]

/-- Prefix replay is the internal paired-state trajectory. Beyond the tape it holds the endpoint;
that mathematical extension does not add semantic steps. -/
noncomputable def executionTrajectory (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) (position : ℕ) : Option ExecutionState :=
  replayEvents? policy program source (events.take position)

@[simp] theorem executionTrajectory_zero (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) :
    executionTrajectory policy program source events 0 = some source := rfl

/-- Valid paths authenticate the state returned at every semantic cut. -/
theorem ExecutionPath.replay_split {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) (cut : ℕ) :
    ∃ middle, executionTrajectory policy program source events cut = some middle ∧
      ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target := by
  obtain ⟨middle, left, right⟩ := path.split cut
  exact ⟨middle, left.replay, left, right⟩

end SP1Clean.Model.Core
