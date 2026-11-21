module

public import SP1Clean.Semantics.Resources.ExecutionResources

/-! # Persistent hint inventories on a complete mixed execution

The queue projection uses each actual replay step once. Its allocation frontier counts guest
and hook hints throughout the segment, including nodes removed from the live queue by a read.
The initial store may contain historical nodes from an earlier segment.
-/

@[expose] public section

namespace SP1Clean.Semantics.HintQueue

open Machine Soundness.Target

/-- Advance the persistent cursor at one pair of adjacent replayed host states. -/
def advance? (source target : HostState) (cursor : Store × ℕ) :
    ExecutionEvent → Option (Store × ℕ)
  | .ordinary => some cursor
  | .syscall call => do
    let kind ← SyscallKind.decode? call.rawCode
    (source.hintUpdate kind target).apply? cursor.1 cursor.2

/-- Project the existing Sail/host replay to an immutable hint store and its current head. -/
noncomputable def storeAfter? (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → Store × ℕ → Option (Store × ℕ)
  | _, [], cursor => some cursor
  | source, event :: rest, cursor => do
    let middle ← replayStep? policy program source event
    let next ← advance? source.host middle.host cursor event
    storeAfter? policy program middle rest next

variable {policy : HostPolicy} {program : GuestProgram}
  {source middle target : ExecutionState} {event : ExecutionEvent}
  {events first second : List ExecutionEvent}

private theorem step_store (step : ExecutionStep policy program source event target)
    {cursor : Store × ℕ} (valid : WellFormed cursor.1)
    (represented : Represents cursor.1 cursor.2 source.host.io.hints) :
    ∃ next, advance? source.host target.host cursor event = some next ∧
      Extends cursor.1 next.1 ∧ WellFormed next.1 ∧ Represents next.1 next.2 target.host.io.hints ∧
      next.1.size = cursor.1.size + source.eventResources policy event .allocatedHints := by
  cases step with
  | ordinary => exact ⟨cursor, rfl, .refl _, valid, represented, rfl⟩
  | syscall step =>
    obtain ⟨pc, execution, _, _, ran, rfl, rfl, rfl⟩ := HostState.step_observations step
    obtain ⟨⟨store, head⟩, applied, rep⟩ := HostState.hintUpdate_sound ran represented
    have decoded := (SyscallKind.decode?_eq_some_iff execution.kind.code execution.kind).mpr rfl
    refine ⟨(store, head), ?_, Update.apply?_extends applied,
      (Update.apply?_valid valid represented.bound applied).1, rep, ?_⟩
    · simpa only [advance?, HostExecution.toEvent, decoded, Option.bind_eq_bind, Option.bind_some] using applied
    · rw [Update.apply?_size applied]
      congr 1
      simp only [ExecutionState.eventResources, HostState.eventResources, ran, HostState.executionResources]
      by_cases length : execution.kind = .hintLength
      · have actual := ((source.host.run_eq_some_iff policy _ execution).mp ran).2.2.2.2.2
        rw [length] at actual
        have result := (Option.some.inj actual).symm
        simp [HostState.hintUpdate, HostState.hintEvent, length, result, Event.allocations, Update.allocations]
      · by_cases read : execution.kind = .hintRead <;>
          simp [HostState.hintUpdate, HostState.hintEvent, length, read, Event.allocations, Update.allocations]

/-- Every mixed path produces the exact final live queue, preserves all earlier nodes, and grows
the allocation frontier by the measured cumulative allocation cost. -/
theorem storeAfter_of_path (path : ExecutionPath policy program source events target)
    {cursor : Store × ℕ} (valid : WellFormed cursor.1)
    (represented : Represents cursor.1 cursor.2 source.host.io.hints) :
    ∃ next, storeAfter? policy program source events cursor = some next ∧
      Extends cursor.1 next.1 ∧ WellFormed next.1 ∧ Represents next.1 next.2 target.host.io.hints ∧
      next.1.size = cursor.1.size + executionResources policy program source events .allocatedHints := by
  induction path generalizing cursor with
  | nil => exact ⟨cursor, rfl, .refl _, valid, represented, rfl⟩
  | @cons before mid last e rest step _ ih =>
    obtain ⟨afterStep, applied, extension, valid', rep', size⟩ := step_store step valid represented
    obtain ⟨final, built, restExtension, valid'', rep'', restSize⟩ := ih valid' rep'
    refine ⟨final, ?_, extension.trans restExtension, valid'', rep'', ?_⟩
    · simp only [storeAfter?, step.replay, Option.bind_eq_bind, Option.bind_some, applied, built]
    · rw [executionResources_cons step, restSize, size]
      simp [ResourceUsage.combine, ResourceKind.cumulative, ExecutionState.resources, Nat.add_assoc]

/-- A cut continues from the same persistent store, including every allocation preceding the cut. -/
theorem storeAfter_append (path : ExecutionPath policy program source first middle) (cursor : Store × ℕ) :
    storeAfter? policy program source (first ++ second) cursor =
      (storeAfter? policy program source first cursor).bind (storeAfter? policy program middle second) := by
  induction path generalizing cursor with
  | nil => rfl
  | @cons before mid last e rest step _ ih =>
    simp only [List.cons_append, storeAfter?, step.replay, Option.bind_eq_bind, Option.bind_some]
    cases result : advance? before.host mid.host cursor e with
    | none => rfl
    | some next => exact ih next

/-- Starting from a canonical finite source constructs the queue at every cut and carries that
very store to the end. The prefix frontier counts every allocation, even after multiple pops. -/
theorem storeAfter_at (path : ExecutionPath policy program source events target) (cut : ℕ) :
    ∃ reached cursor final,
      ExecutionPath policy program source (events.take cut) reached ∧
      storeAfter? policy program source (events.take cut) (ofList source.host.io.hints) = some cursor ∧
      Represents cursor.1 cursor.2 reached.host.io.hints ∧
      cursor.1.size = source.host.io.hints.length +
        executionResources policy program source (events.take cut) .allocatedHints ∧
      storeAfter? policy program reached (events.drop cut) cursor = some final ∧
      storeAfter? policy program source events (ofList source.host.io.hints) = some final ∧
      Extends cursor.1 final.1 ∧ Represents final.1 final.2 target.host.io.hints := by
  obtain ⟨reached, firstPath, lastPath⟩ := path.split cut
  obtain ⟨cursor, start, _, valid, rep, size⟩ := storeAfter_of_path firstPath
    (ofList_wellFormed source.host.io.hints) (ofList_represents source.host.io.hints)
  obtain ⟨final, finish, extension, _, finalRep, _⟩ := storeAfter_of_path lastPath valid rep
  refine ⟨reached, cursor, final, firstPath, start, rep, (ofList_size _ ▸ size), finish, ?_, extension, finalRep⟩
  have combined := storeAfter_append (second := events.drop cut) firstPath (ofList source.host.io.hints)
  simpa only [List.take_append_drop, start, Option.bind_some, finish] using combined

end SP1Clean.Semantics.HintQueue
