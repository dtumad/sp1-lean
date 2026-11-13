import SP1Clean.Model.Machine.Syscall

/-! # Execution event labels

Labels of the steps of `ExecutionPath`: an ordinary official-Sail instruction, or a host syscall
carrying its observed `CoreSyscallEvent`. Each label selects its interaction-clock window (eight
ticks for an instruction, `CLK_INC + 256 = 264` for a syscall). The step relation itself is
`Model.Core.ExecutionStep`. A `LocatedTransition` pairs a label and its target with the source
state; the instruction-event compiler consumes these proof-free records. -/

open LeanRV64D

namespace SP1Clean.Machine

open SP1Clean.Soundness.Target

/-- Stable label of one semantic step. -/
inductive ExecutionEvent
  | ordinary
  | syscall (event : CoreSyscallEvent)
deriving DecidableEq, Repr

/-- The upstream clock window selected by an event. -/
def ExecutionEvent.schedule : ExecutionEvent → StepSchedule
  | .ordinary => ordinarySchedule
  | .syscall _ => syscallSchedule

/-- Width of an event's interaction-clock window. -/
def ExecutionEvent.duration (event : ExecutionEvent) : ℕ :=
  event.schedule.duration

/-- The event's own timestamp, when it carries one, agrees with the beginning of its schedule
window.  Ordinary events obtain their clock from ordered State rows and therefore carry no duplicate
field here. -/
def ExecutionEvent.StartsAt (clock : ℕ) : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall event => event.clock = clock

@[simp] theorem ExecutionEvent.duration_ordinary : ExecutionEvent.ordinary.duration = 8 := rfl

@[simp] theorem ExecutionEvent.duration_syscall (event : CoreSyscallEvent) :
    (ExecutionEvent.syscall event).duration = 264 := rfl

/-- Ordinary-arm test on one event, as a `Bool` so a shard's ordinary-row count is computable
without a decidability instance for `CoreSyscallEvent`. -/
def ExecutionEvent.isOrdinary : ExecutionEvent → Bool
  | .ordinary => true
  | .syscall _ => false

@[simp] theorem ExecutionEvent.isOrdinary_ordinary :
    ExecutionEvent.ordinary.isOrdinary = true := rfl

@[simp] theorem ExecutionEvent.isOrdinary_syscall (event : CoreSyscallEvent) :
    (ExecutionEvent.syscall event).isOrdinary = false := rfl

/-- Proof-free data for one transition in an extracted semantic trace. -/
structure EventTransition where
  event : ExecutionEvent
  target : SailState

/-- One proof-free transition together with the source state at which it occurs. The target remains
the one stored by `EventTransition`; this is a derived chronological view, not a second trace. -/
structure LocatedTransition where
  source : SailState
  transition : EventTransition

/-- Attach each transition to its source state, threading targets in execution order. -/
def locateTransitions : SailState → List EventTransition → List LocatedTransition
  | _, [] => []
  | source, transition :: rest =>
      ⟨source, transition⟩ :: locateTransitions transition.target rest

@[simp] theorem locateTransitions_length (source : SailState)
    (transitions : List EventTransition) :
    (locateTransitions source transitions).length = transitions.length := by
  induction transitions generalizing source with
  | nil => rfl
  | cons transition rest ih => simp [locateTransitions, ih]

@[simp] theorem locateTransitions_map_transition (source : SailState)
    (transitions : List EventTransition) :
    (locateTransitions source transitions).map LocatedTransition.transition = transitions := by
  induction transitions generalizing source with
  | nil => rfl
  | cons transition rest ih => simp [locateTransitions, ih]

end SP1Clean.Machine
