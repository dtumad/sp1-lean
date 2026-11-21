module

public import SP1Clean.Semantics.Resources.ExecutionResources

/-! # HINT_READ word demand of a complete execution

The actual syscall label carries the byte length of its authenticated queue item. A successful
read pays for its full words and exactly one final padded word. All eight host handlers are
covered, including WRITE, which reads guest RAM but does not write it.
-/

@[expose] public section

namespace SP1Clean.Semantics.HintReadDemand

open Machine

/-- Requested byte length, only on the complete released HINT_READ code. -/
def length? : ExecutionEvent → Option ℕ
  | .ordinary => none
  | .syscall call => if call.rawCode = SyscallKind.hintRead.code then some call.arg2.toNat else none

/-- Number of nonterminal word transfers. The number of final transfers is the list length. -/
def continuing (lengths : List ℕ) : ℕ := (lengths.map (· / 8)).sum

private theorem step_writeBytes {source target : ExecutionState} {event : ExecutionEvent}
    {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    (step : ExecutionStep policy program source event target) :
    source.eventResources policy event .writeBytes = ((length? event).map (fun n => 8 * (n / 8 + 1))).getD 0 := by
  cases step with
  | ordinary => rfl
  | syscall success =>
    obtain ⟨pc, run, _, _, ran, _, _, rfl⟩ := HostState.step_observations success
    have effect := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
    simp only [ExecutionState.eventResources, HostState.eventResources, ran, HostState.executionResources, length?,
      HostExecution.toEvent]
    by_cases read : run.kind = .hintRead
    · simp only [read, ↓reduceIte, Option.map_some, Option.getD_some]
      rw [read] at effect
      obtain ⟨bytes, _, _, size, _, _, eq⟩ := (HostState.execute_hintRead_iff ..).mp effect
      simp [HostExecution.writeByteCount, HostExecution.writeSpans, eq, hintWriteBytes_length, size]
    · have code : run.kind.code ≠ SyscallKind.hintRead.code := fun h => read (SyscallKind.code_injective h)
      simp only [code, ↓reduceIte, Option.map_none, Option.getD_none]
      cases kind : run.kind <;> rw [kind] at effect
      case hintRead => exact (read kind).elim
      case write =>
        obtain ⟨_, _, _, _, _, _, eq⟩ := (HostState.execute_write_iff ..).mp effect
        simp [HostExecution.writeByteCount, HostExecution.writeSpans, eq]
      all_goals
        simp only [HostState.executeKind] at effect
        try split_ifs at effect
        all_goals
          obtain eq := (Option.some.inj effect).symm
          simp [HostExecution.writeByteCount, HostExecution.writeSpans, eq]

/-- The guest write charge pays exactly eight bytes for every transfer. This equality uses
the actual tape and includes the mandatory final word for empty and word-aligned hints. -/
theorem writeBytes {source target : ExecutionState} {events : List ExecutionEvent}
    {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    (path : ExecutionPath policy program source events target) :
    executionResources policy program source events .writeBytes =
      8 * (continuing (events.filterMap length?) + (events.filterMap length?).length) := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
    rw [executionResources_cons step]
    simp only [ResourceUsage.combine, ResourceKind.cumulative, ↓reduceIte, ExecutionState.resources,
      step_writeBytes step, ih]
    cases h : length? _ with
    | none => simp [h]
    | some n => simp [h, continuing]; omega

end SP1Clean.Semantics.HintReadDemand
