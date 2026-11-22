module

public import SP1Clean.Semantics.Resources.HintAllocations
public import SP1Clean.Semantics.Resources.HintReadDemand
public import SP1Clean.Semantics.Host.HintQueueWords

/-! # Historical bytes and padded words in the persistent hint store

WRITE prepends the same buffers to the queue and the immutable store, including an ordered
hook reply. HINT_READ removes one buffer from the live queue and retains the node. Its guest
write pays for all the removed buffer's padded words. The equalities below count occurrences
in the original store, so duplicate buffers and already-popped nodes retain their costs.
-/

@[expose] public section

namespace SP1Clean.Semantics.HintQueue
open Machine Soundness.Target

variable {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
  {event : ExecutionEvent} {events : List ExecutionEvent} {cursor next : Store × ℕ}

private abbrev measured (weight : ℕ → ℕ) (buffers : List Bytes) : ℕ :=
  (buffers.map (fun bytes => weight bytes.length)).sum

private theorem step_measure (weight : ℕ → ℕ) (step : ExecutionStep policy program source event target)
    (advanced : advance? source.host target.host cursor event = some next) :
    measured weight (next.1.toList.map Node.bytes) + measured weight source.host.io.hints =
      measured weight (cursor.1.toList.map Node.bytes) + measured weight target.host.io.hints +
        ((HintReadDemand.length? event).map weight).getD 0 := by
  cases step with
  | ordinary => obtain rfl := Option.some.inj advanced; simp [HintReadDemand.length?]
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, rfl, rfl, rfl⟩ := HostState.step_observations success
    have decoded := (SyscallKind.decode?_eq_some_iff execution.kind.code execution.kind).mpr rfl
    have executed := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
    simp only [advance?, HostExecution.toEvent, decoded, Option.bind_eq_bind, Option.bind_some] at advanced
    by_cases read : execution.kind = .hintRead
    · rw [read] at executed
      obtain ⟨bytes, rest, live, length, _, _, effect⟩ := (HostState.execute_hintRead_iff ..).mp executed
      simp only [HostState.hintUpdate, ite_eq_left read, Update.apply?] at advanced
      obtain ⟨pair, _, same⟩ := Option.map_eq_some_iff.mp advanced
      have store : next.1 = cursor.1 := (congrArg Prod.fst same).symm
      simp only [store, live, effect, measured, List.map_cons, List.sum_cons, HintReadDemand.length?,
        HostExecution.toEvent, read, ↓reduceIte, Option.map_some, Option.getD_some, length]
      omega
    · obtain ⟨added, live⟩ := HostState.executeKind_hintSuffix executed read
      simp only [HostState.hintUpdate, ite_eq_right read, live, List.length_append, Nat.add_sub_cancel_right,
        List.take_left, Update.apply?] at advanced
      obtain rfl := (Option.some.inj advanced).symm
      have code : execution.kind.code ≠ SyscallKind.hintRead.code := fun eq => read (SyscallKind.code_injective eq)
      simp only [prepend_bytes, measured, List.map_append, List.map_reverse, List.sum_append, List.sum_reverse,
        live, HintReadDemand.length?, HostExecution.toEvent, code, ↓reduceIte, Option.map_none, Option.getD_none]
      omega

private theorem storeAfter_measure_aux (weight : ℕ → ℕ) (path : ExecutionPath policy program source events target)
    (built : storeAfter? policy program source events cursor = some next) :
    measured weight (next.1.toList.map Node.bytes) + measured weight source.host.io.hints =
      measured weight (cursor.1.toList.map Node.bytes) + measured weight target.host.io.hints +
        ((events.filterMap HintReadDemand.length?).map weight).sum := by
  induction path generalizing cursor with
  | nil => obtain rfl := Option.some.inj built; simp
  | @cons before mid after e tape step _ ih =>
    simp only [storeAfter?, step.replay, Option.bind_eq_bind, Option.bind_some] at built
    obtain ⟨atStep, advanced, remaining⟩ := Option.bind_eq_some_iff.mp built
    have first := step_measure weight step advanced
    have rest := ih remaining
    cases demand : HintReadDemand.length? e <;>
      simp [demand] at first ⊢ <;> omega

/-- The final store consists in measure of the live target queue plus the actual popped
buffers. This holds for any weight on byte lengths and every complete eight-call path. -/
theorem storeAfter_measure (weight : ℕ → ℕ) (path : ExecutionPath policy program source events target)
    (built : storeAfter? policy program source events (ofList source.host.io.hints) = some next) :
    (((next.1.toList.map Node.bytes).map fun bytes => weight bytes.length).sum) =
      (target.host.io.hints.map fun bytes => weight bytes.length).sum +
        ((events.filterMap HintReadDemand.length?).map weight).sum := by
  have total := storeAfter_measure_aux weight path built
  simp only [measured, ofList_bytes, List.map_reverse, List.sum_reverse] at total
  omega

/-- Original bytes in all immutable nodes, including the popped portion of the store. -/
def storedByteCount (store : Store) : ℕ := ((store.toList.map Node.bytes).map List.length).sum

/-- Word rows for all immutable nodes, with a mandatory padded final word for every buffer. -/
def storedWordCount (store : Store) : ℕ := ((store.toList.map Node.bytes).map wordCount).sum

/-- The remaining queue and the exact guest write charge account for the entire native
history. No WRITE-length assumption is needed for request-bound hook replies. -/
theorem storeAfter_totals (path : ExecutionPath policy program source events target)
    (built : storeAfter? policy program source events (ofList source.host.io.hints) = some next) :
    storedByteCount next.1 = (target.host.io.hints.map List.length).sum +
      (events.filterMap HintReadDemand.length?).sum ∧
    8 * storedWordCount next.1 = 8 * (target.host.io.hints.map wordCount).sum +
      executionResources policy program source events .writeBytes := by
  have raw := storeAfter_measure id path built
  have padded := storeAfter_measure (fun length => length / 8 + 1) path built
  change storedWordCount next.1 = (target.host.io.hints.map wordCount).sum + _ at padded
  have markers (lengths : List ℕ) : (lengths.map fun n => n / 8 + 1).sum =
      HintReadDemand.continuing lengths + lengths.length := by
    induction lengths with
    | nil => rfl
    | cons n tail ih => simp only [HintReadDemand.continuing, List.map_cons, List.sum_cons, List.length_cons] at *; omega
  rw [markers] at padded
  refine ⟨by simpa only [storedByteCount, id_eq, List.map_id_fun] using raw, ?_⟩
  rw [HintReadDemand.writeBytes path]
  omega

end SP1Clean.Semantics.HintQueue
