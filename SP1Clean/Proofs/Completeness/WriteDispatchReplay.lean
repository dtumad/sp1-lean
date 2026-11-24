import SP1Clean.Proofs.Completeness.WriteDispatchTable

/-! # Chronological construction of every WRITE dispatch input

The compiler visits each CPU event once. The canonical replay supplies the next machine state
and queue cursor. Missing a required guest read fails the construction at that event. The
result agrees in order and multiplicity with the positional characterization of the table.
-/

namespace SP1Clean.WriteEffects

open Semantics Machine FormalModel.Shard TraceGen
private abbrev F := ZMod SP1Prime

private def emit (origin : HostState) (previous : Nat) (current : ExecutionState) (store : HintQueue.Store) :
    ExecutionEvent → Option WriteObservations.Packet → Option (Dispatch F)
  | .syscall call, some (length, _) =>
    some (dispatchRow call.arg1 call.arg2 length current.clock previous
      (WriteStreams.fromEndpoints origin current.host) current.host store)
  | _, _ => none

/-- A single replay carries the previous WRITE clock and the persistent hint cursor through
all event kinds. The full observational read succeeds before an active row can be emitted. -/
noncomputable def dispatchTape? (image : ProgramImage) (origin : HostState) :
    Nat → ExecutionState → HintQueue.Store × Nat → List ExecutionEvent → Option (List (Dispatch F))
  | _, _, _, [] => some []
  | previous, current, cursor, event :: rest => do
    let policy := FormalModel.Shard.policy SP1Prime image
    let next ← replayStep? policy image.program current event
    let advanced ← HintQueue.advance? current.host next.host cursor event
    let observation ← WriteObservations.packetAt? current.sail event
    let tail ← dispatchTape? image origin (advanceWriteClock previous event) next advanced rest
    return (emit origin previous current cursor.1 event observation).toList ++ tail

private theorem at_succ (image : ProgramImage) (origin : HostState) (previous : Nat) (source next : ExecutionState)
    (cursor advanced : HintQueue.Store × Nat) (head : ExecutionEvent) (rest : List ExecutionEvent)
    (step : replayStep? (policy SP1Prime image) image.program source head = some next)
    (advance : HintQueue.advance? source.host next.host cursor head = some advanced) (e : ExecutionEvent) (i : Nat) :
    dispatchAt? image origin previous source cursor (head :: rest) (e,i+1) =
      dispatchAt? image origin (advanceWriteClock previous head) next advanced rest (e,i) := by
  cases e with
  | ordinary => rfl
  | syscall call =>
    by_cases code : call.rawCode = SyscallKind.write.code
    · simp [dispatchAt?, code, executionTrajectory, replayEvents?, step, HintQueue.storeAfter?, advance]
    · simp [dispatchAt?, code]

private theorem at_zero (image : ProgramImage) (origin : HostState) (previous : Nat) (source : ExecutionState)
    (cursor : HintQueue.Store × Nat) (head : ExecutionEvent) (rest : List ExecutionEvent) {obs : Option WriteObservations.Packet}
    (observed : WriteObservations.packetAt? source.sail head = some obs) :
    dispatchAt? image origin previous source cursor (head :: rest) (head,0) = emit origin previous source cursor.1 head obs := by
  cases head with
  | ordinary => cases observed; rfl
  | syscall call =>
    by_cases code : call.rawCode = SyscallKind.write.code
    · simp only [WriteObservations.packetAt?, ite_eq_left code, Option.map_eq_some_iff] at observed
      obtain ⟨⟨len, words⟩, read, rfl⟩ := observed
      simp [dispatchAt?, code, executionTrajectory, replayEvents?, HintQueue.storeAfter?, read, emit]
    · simp only [WriteObservations.packetAt?, ite_eq_right code, Option.some.injEq] at observed
      subst obs
      simp [dispatchAt?, code, emit]

private theorem tape_eq {image : ProgramImage} (origin : HostState) {source : ExecutionState}
    {events : List ExecutionEvent} (previous : Nat) {cursor final : HintQueue.Store × Nat}
    (store : HintQueue.storeAfter? (policy SP1Prime image) image.program source events cursor = some final)
    {packets : List WriteObservations.Packet}
    (reads : WriteObservations.packets? (policy SP1Prime image) image.program source events = some packets) :
    dispatchTape? image origin previous source cursor events =
      some (events.zipIdx.filterMap (dispatchAt? image origin previous source cursor events)) := by
  induction events generalizing source previous cursor packets with
  | nil => rfl
  | cons event rest ih =>
    simp only [HintQueue.storeAfter?, Option.bind_eq_bind, Option.bind_eq_some_iff] at store
    obtain ⟨next, step, advanced, advance, remain⟩ := store
    simp only [WriteObservations.packets?, step, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at reads
    obtain ⟨observation, observed, tail, tailRead, _⟩ := reads
    have compiled := ih (advanceWriteClock previous event) remain tailRead
    rw [List.zipIdx_cons', List.filterMap_cons, List.filterMap_map]
    have align :
        dispatchAt? image origin previous source cursor (event :: rest) ∘ Prod.map id (· + 1) =
          dispatchAt? image origin (advanceWriteClock previous event) next advanced rest := by
      funext ⟨e,i⟩
      exact at_succ image origin previous source next cursor advanced event rest step advance e i
    rw [align, at_zero image origin previous source cursor event rest observed]
    simp only [dispatchTape?, step, advance, observed, compiled, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    cases emit origin previous source cursor.1 event observation <;> rfl

/-- The one-pass compiler succeeds on every admissible mixed shard and returns exactly the
certified dispatcher inputs, in the order of the original execution. -/
theorem native_dispatch_replay {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    dispatchTape? image source.host source.clock source.realize (HintQueue.ofList source.host.io.hints) events =
      some (dispatchInputs image source events) := by
  obtain ⟨_, store, _⟩ := HintQueue.storeAfter_of_path run.1.2 (HintQueue.ofList_wellFormed _) (HintQueue.ofList_represents _)
  obtain ⟨_, reads⟩ := WriteObservations.admissible_packets run
  exact tape_eq source.host source.clock store reads

end SP1Clean.WriteEffects
