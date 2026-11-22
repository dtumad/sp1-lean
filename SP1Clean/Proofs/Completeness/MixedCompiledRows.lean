import SP1Clean.Proofs.Completeness.MixedAccessFrontier

/-! # Compiled instruction and syscall rows in tape order

Each entry retains the data produced at its own mixed execution cut. Physical table projections
can select their rows from this list while using the same register-access frontier.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

/-- The ordinary compiler output or the inputs to the ECALL compiler at a single tape cut. -/
inductive MixedCompiledRow where
  /-- An ordinary instruction with its scheduled register accesses and routed physical row. -/
  | ordinary (row : CompiledInstructionEvent)
  /-- An ECALL with the incoming register-access frontier and the clock of the pre-state. -/
  | syscall (frontier : AccessFrontier) (base : ℕ) (call : CoreSyscallEvent)

/-- Compile each event using the frontier produced by its immediate predecessor. -/
noncomputable def routeMixedRows? (host : HostPolicy) (program : GuestProgram) :
    AccessFrontier → ExecutionState → List ExecutionEvent → Option (List MixedCompiledRow)
  | _, _, [] => some []
  | frontier, current, event :: later =>
    emitMixedAccessStep? host program (current, frontier) event
      (fun next row => do
        let tail ← routeMixedRows? host program row.nextFrontier next later
        return .ordinary row :: tail)
      (fun next call => do
        let tail ← routeMixedRows? host program (syscallFrontier frontier current.clock call) next later
        return .syscall frontier current.clock call :: tail)

/-- A compiled entry belongs to the semantic successor of this exact prefix and uses its frontier. -/
theorem routeMixedRows?_at {host : HostPolicy} {program : GuestProgram} {frontier : AccessFrontier}
    {current : ExecutionState} {events : List ExecutionEvent} {inputs : List MixedCompiledRow}
    (routed : routeMixedRows? host program frontier current events = some inputs)
    {cut : ℕ} {event : ExecutionEvent} (present : events[cut]? = some event) :
    ∃ before incoming next,
      (events.take cut).foldlM (mixedAccessStep host program) (current, frontier) = some (before, incoming) ∧
      replayStep? host program before event = some next ∧
      match event with
      | .ordinary => ∃ view row, projectSP1Transition? program ⟨before.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
          compileInstructionEvent? view incoming before.clock = some row ∧ inputs[cut]? = some (.ordinary row)
      | .syscall call => inputs[cut]? = some (.syscall incoming before.clock call) := by
  induction events generalizing current frontier inputs cut with
  | nil => simp at present
  | cons head tail ih =>
    simp only [routeMixedRows?, emitMixedAccessStep?, Option.bind_eq_bind, Option.bind_eq_some_iff] at routed
    obtain ⟨middle, step, built⟩ := routed
    cases head with
    | ordinary =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at built
      obtain ⟨view, seen, row, made, later, rest, rfl⟩ := built
      cases cut with
      | zero =>
        cases present
        exact ⟨current, frontier, middle, rfl, step, view, row, seen, made, rfl⟩
      | succ cut =>
        obtain ⟨s, f, next, reached, replay, atRow⟩ := ih rest present
        exact ⟨s, f, next, by simpa [mixedAccessStep, emitMixedAccessStep?, step, seen, made] using reached, replay,
          by cases event <;> exact atRow⟩
    | syscall call =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at built
      obtain ⟨later, rest, rfl⟩ := built
      cases cut with
      | zero =>
        cases present
        exact ⟨current, frontier, middle, rfl, step, rfl⟩
      | succ cut =>
        obtain ⟨s, f, next, reached, replay, atRow⟩ := ih rest present
        exact ⟨s, f, next, by simpa [mixedAccessStep, emitMixedAccessStep?, step] using reached, replay,
          by cases event <;> exact atRow⟩

end SP1Clean.TraceGen
