module

public import SP1Clean.FormalModel.SupportedShard
public import SP1Clean.Model.Semantics.TransitionDecode
public import SP1Clean.Proofs.Completeness.InstructionEvent

/-!
# Chronological ordinary-execution compiler

This is the total, proof-independent fold from the `Machine.EventExecutionTrace` deterministically
evaluated from the common shard witness to the chronological instruction/access data consumed by
native trace assembly. Each transition is decoded again from the committed program, compiled through the one
canonical access plan, and scheduled with its required register refreshes.  The result retains the
source `LocatedTransition`, decoded instruction, dependent routed event, access schedule, clock,
and outgoing frontier in one carrier.

The compiler takes no validity proof.  It returns `none` when the semantic witness is outside the
representable native image.  `Execution.NativeCompilerReady` is the transparent success-and-local-
validity predicate: it refers only to the unique result of this function and never to an AIR
witness, a Clean row, or an existential trace generator.
-/

@[expose] public section

open LeanRV64D.Defs

namespace SP1Clean.TraceGen

open SP1Clean.Semantics
open SP1Clean.Soundness.Target

/-- One chronological compiler record, retaining the exact semantic transition it represents. -/
structure CompiledLocatedInstruction where
  located : Machine.LocatedTransition
  view : SP1TransitionView
  clock : ℕ
  instruction : CompiledInstructionEvent

/-- The complete chronological active part of one native ordinary shard. -/
structure CompiledExecution where
  rows : List CompiledLocatedInstruction
  finalClock : ℕ
  finalFrontier : AccessFrontier

namespace CompiledExecution

/-- Registry-indexed events are a stable partition of the one chronological row list. -/
def instructionEvents (compiled : CompiledExecution) : EventBuckets :=
  EventBuckets.ofChronological (compiled.rows.map fun row => row.instruction.routed)

/-- Routing preserves occurrences and cannot enlarge an instruction's physical input list. -/
theorem instructionEvents_length_le (compiled : CompiledExecution) (id : InstructionChipId) :
    (compiled.instructionEvents id).length ≤ compiled.rows.length := by
  exact (EventBuckets.length_le _ id).trans (List.length_map _).le

/-- MemoryBump events remain in chronological row/role order. -/
def memoryBumps (compiled : CompiledExecution) : List MemoryBumpEvent :=
  compiled.rows.flatMap fun row => row.instruction.memoryBumps

/-- The chronological access schedules, without reconstructing event fields. -/
def accessSchedules (compiled : CompiledExecution) : List AccessSchedule :=
  compiled.rows.map fun row => row.instruction.schedule

/-- Transparent native representability of the deterministic compiler result.

The instruction clause is stated on the exact registry buckets consumed by trace assembly.  The
refresh clause is stated on the exact chronological list consumed by the MemoryBump table. -/
structure WellFormed (compiled : CompiledExecution) : Prop where
  instruction : ∀ id event, event ∈ compiled.instructionEvents id → id.Valid event
  memoryBumps : ∀ event ∈ compiled.memoryBumps, event.WellFormed

end CompiledExecution

/-- Fold already-located transitions from one clock/frontier state. -/
noncomputable def compileLocatedTransitions? (program : GuestProgram) :
    ℕ → AccessFrontier → List Machine.LocatedTransition → Option CompiledExecution
  | clock, frontier, [] =>
      some { rows := [], finalClock := clock, finalFrontier := frontier }
  | clock, frontier, located :: rest => do
      let view ← projectSP1Transition? program located
      let instruction ← compileInstructionEvent? view frontier clock
      let tail ← compileLocatedTransitions? program (clock + ordinaryClkInc)
        instruction.nextFrontier rest
      pure
        { rows := { located := located
                    view := view
                    clock := clock
                    instruction := instruction } :: tail.rows
          finalClock := tail.finalClock
          finalFrontier := tail.finalFrontier }

/-- Compile the chronological trace view evaluated from a common shard witness. The existing
ordinary-shard limit is checked before constructing physical tables; oversized transcripts are
outside that semantic domain and return `none`, without truncating any admitted execution. -/
noncomputable def compileExecution? (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) : Option CompiledExecution :=
  if execution.steps ≤ Model.Core.Profile.maxOrdinaryTransitions then
    compileLocatedTransitions? program initialClock AccessFrontier.initial execution.locatedTransitions
  else none

/-- On the existing semantic domain, the capacity check preserves the complete chronological fold.
Success also supplies the bound needed by physical construction, without a caller proof input. -/
theorem compileExecution?_eq_some_iff (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) (compiled : CompiledExecution) :
    compileExecution? program execution initialClock = some compiled ↔
      Model.Core.Profile.WithinOrdinaryRowLimit execution.steps ∧
        compileLocatedTransitions? program initialClock AccessFrontier.initial
          execution.locatedTransitions = some compiled := by
  unfold compileExecution? Model.Core.Profile.WithinOrdinaryRowLimit
  split <;> simp_all

/-- Harmless total fallback used only off the compiler's supported image.  The public
`NativeCompilerReady` predicate proves that the optional compiler returned `some`, so every theorem
about an admissible execution rewrites this fallback away. -/
def emptyCompiledExecution (initialClock : ℕ) : CompiledExecution where
  rows := []
  finalClock := initialClock
  finalFrontier := AccessFrontier.initial

/-- Total, proof-independent compiler result.  Functional completeness maps may depend on the
statement and semantic witness, but never on a proof that the witness is admissible; using `getD`
makes that separation visible in the definition. -/
noncomputable def compileExecution (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) : CompiledExecution :=
  (compileExecution? program execution initialClock).getD (emptyCompiledExecution initialClock)

theorem compileExecution_eq_of_some {program : GuestProgram}
    {execution : Machine.EventExecutionTrace} {initialClock : ℕ} {compiled : CompiledExecution}
    (generated : compileExecution? program execution initialClock = some compiled) :
    compileExecution program execution initialClock = compiled := by
  simp [compileExecution, generated]

@[simp] theorem compileLocatedTransitions?_nil (program : GuestProgram)
    (clock : ℕ) (frontier : AccessFrontier) :
    compileLocatedTransitions? program clock frontier [] =
      some { rows := [], finalClock := clock, finalFrontier := frontier } := rfl

/-- A successful fold preserves the number of semantic transitions exactly. -/
theorem compileLocatedTransitions?_rows_length
    {program : GuestProgram} {clock : ℕ} {frontier : AccessFrontier}
    {transitions : List Machine.LocatedTransition} {compiled : CompiledExecution}
    (generated : compileLocatedTransitions? program clock frontier transitions = some compiled) :
    compiled.rows.length = transitions.length := by
  induction transitions generalizing clock frontier compiled with
  | nil =>
      simp only [compileLocatedTransitions?, Option.some.injEq] at generated
      subst compiled
      rfl
  | cons located rest ih =>
      simp only [compileLocatedTransitions?] at generated
      cases projectionEq : projectSP1Transition? program located with
      | none => simp [projectionEq] at generated
      | some view =>
          simp only [projectionEq] at generated
          cases instructionEq : compileInstructionEvent? view frontier clock with
          | none => simp [instructionEq] at generated
          | some instruction =>
              simp [instructionEq] at generated
              cases tailEq : compileLocatedTransitions? program (clock + ordinaryClkInc)
                  instruction.nextFrontier rest with
              | none => simp [tailEq] at generated
              | some tail =>
                  simp [tailEq] at generated
                  subst compiled
                  simp only [List.length_cons]
                  exact congrArg Nat.succ (ih tailEq)

/-- The total compiler never emits more instruction rows than the semantic transcript contains. -/
theorem compileExecution_rows_length_le (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (compileExecution program execution initialClock).rows.length ≤ execution.steps := by
  cases generated : compileExecution? program execution initialClock with
  | none => simp [compileExecution, generated, emptyCompiledExecution]
  | some compiled =>
      rw [compileExecution_eq_of_some generated]
      simpa only [Machine.EventExecutionTrace.locatedTransitions_length] using
        (compileLocatedTransitions?_rows_length
          ((compileExecution?_eq_some_iff ..).mp generated).2).le

/-- Every total compiler result fits the existing semantic row limit. On a failed or oversized
input the result is empty; on success the check above certifies the unchanged complete fold. -/
theorem compileExecution_rows_length_le_limit (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    Model.Core.Profile.WithinOrdinaryRowLimit
      (compileExecution program execution initialClock).rows.length := by
  cases generated : compileExecution? program execution initialClock with
  | none =>
      simp [compileExecution, generated, emptyCompiledExecution,
        Model.Core.Profile.WithinOrdinaryRowLimit]
  | some compiled =>
      exact (compileExecution_rows_length_le program execution initialClock).trans
        ((compileExecution?_eq_some_iff ..).mp generated).1

/-- The existing semantic shard limit supplies Clean's instruction-table capacity.
No additional compiler footprint or physical readiness premise is required. Provider expansion
and padding have separate bounds; this theorem concerns the unpadded instruction buckets. -/
theorem compileExecution_instruction_capacity (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) (id : InstructionChipId) :
    ((compileExecution program execution initialClock).instructionEvents id).length ≤ UInt64.size := by
  exact ((CompiledExecution.instructionEvents_length_le _ id).trans
    (compileExecution_rows_length_le_limit program execution initialClock)).trans
      (show Model.Core.Profile.maxOrdinaryTransitions ≤ UInt64.size from by decide)

/-- The retained semantic transitions are exactly the input list, in order. -/
theorem compileLocatedTransitions?_located
    {program : GuestProgram} {clock : ℕ} {frontier : AccessFrontier}
    {transitions : List Machine.LocatedTransition} {compiled : CompiledExecution}
    (generated : compileLocatedTransitions? program clock frontier transitions = some compiled) :
    compiled.rows.map CompiledLocatedInstruction.located = transitions := by
  induction transitions generalizing clock frontier compiled with
  | nil =>
      simp only [compileLocatedTransitions?, Option.some.injEq] at generated
      subst compiled
      rfl
  | cons located rest ih =>
      simp only [compileLocatedTransitions?] at generated
      cases projectionEq : projectSP1Transition? program located with
      | none => simp [projectionEq] at generated
      | some view =>
          simp only [projectionEq] at generated
          cases instructionEq : compileInstructionEvent? view frontier clock with
          | none => simp [instructionEq] at generated
          | some instruction =>
              simp [instructionEq] at generated
              cases tailEq : compileLocatedTransitions? program (clock + ordinaryClkInc)
                  instruction.nextFrontier rest with
              | none => simp [tailEq] at generated
              | some tail =>
                  simp [tailEq] at generated
                  subst compiled
                  exact congrArg (located :: ·) (ih tailEq)

/-- The fold advances the public clock by exactly eight ticks per ordinary transition. -/
theorem compileLocatedTransitions?_finalClock
    {program : GuestProgram} {clock : ℕ} {frontier : AccessFrontier}
    {transitions : List Machine.LocatedTransition} {compiled : CompiledExecution}
    (generated : compileLocatedTransitions? program clock frontier transitions = some compiled) :
    compiled.finalClock = clock + ordinaryClkInc * transitions.length := by
  induction transitions generalizing clock frontier compiled with
  | nil =>
      simp only [compileLocatedTransitions?, Option.some.injEq] at generated
      subst compiled
      simp
  | cons located rest ih =>
      simp only [compileLocatedTransitions?] at generated
      cases projectionEq : projectSP1Transition? program located with
      | none => simp [projectionEq] at generated
      | some view =>
          simp only [projectionEq] at generated
          cases instructionEq : compileInstructionEvent? view frontier clock with
          | none => simp [instructionEq] at generated
          | some instruction =>
              simp [instructionEq] at generated
              cases tailEq : compileLocatedTransitions? program (clock + ordinaryClkInc)
                  instruction.nextFrontier rest with
              | none => simp [tailEq] at generated
              | some tail =>
                  simp [tailEq] at generated
                  subst compiled
                  rw [ih tailEq]
                  simp only [List.length_cons]
                  simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

/-- Structural totality of the chronological fold, isolated from per-chip semantic validity.

The shared transition projector and one-row compiler are the only optional steps in the fold. If
each input transition has one projected view whose row-shape compiler succeeds for every incoming
frontier/clock, recursion itself cannot fail. This is the reusable totality lemma behind the
`NativeCompilerReady` campaign; rich `InstructionChipId.Valid` facts remain the separate
`CompiledExecution.WellFormed` half of that boundary. -/
theorem compileLocatedTransitions?_exists_of_views
    {program : GuestProgram} {clock : ℕ} {frontier : AccessFrontier}
    {transitions : List Machine.LocatedTransition}
    (ready : ∀ located ∈ transitions,
      ∃ view : SP1TransitionView,
        projectSP1Transition? program located = some view ∧
          ∀ frontier clock, InstructionEventReady view frontier clock) :
    ∃ compiled, compileLocatedTransitions? program clock frontier transitions = some compiled := by
  induction transitions generalizing clock frontier with
  | nil =>
      exact ⟨{ rows := [], finalClock := clock, finalFrontier := frontier }, rfl⟩
  | cons located rest ih =>
      obtain ⟨view, projected, eventReady⟩ := ready located (by simp)
      obtain ⟨instruction, instructionEq⟩ :=
        instructionEventReady_iff.mp (eventReady frontier clock)
      obtain ⟨tail, tailEq⟩ := ih
        (clock := clock + ordinaryClkInc) (frontier := instruction.nextFrontier)
        (fun item itemMem => ready item (by simp [itemMem]))
      refine ⟨
        { rows := { located := located, view := view, clock := clock,
                    instruction := instruction } :: tail.rows
          finalClock := tail.finalClock
          finalFrontier := tail.finalFrontier }, ?_⟩
      simp [compileLocatedTransitions?, projected, instructionEq, tailEq]

/-- Execution-level form of structural compiler totality. The premise is stated on the literal
`locatedTransitions` view of the one operational witness; no parallel instruction trace is
introduced. -/
theorem compileExecution?_exists_of_views
    {program : GuestProgram} {execution : Machine.EventExecutionTrace} {initialClock : ℕ}
    (bounded : Model.Core.Profile.WithinOrdinaryRowLimit execution.steps)
    (ready : ∀ located ∈ execution.locatedTransitions,
      ∃ view : SP1TransitionView,
        projectSP1Transition? program located = some view ∧
          ∀ frontier clock, InstructionEventReady view frontier clock) :
    ∃ compiled, compileExecution? program execution initialClock = some compiled := by
  obtain ⟨compiled, generated⟩ := compileLocatedTransitions?_exists_of_views ready
  exact ⟨compiled, (compileExecution?_eq_some_iff ..).mpr ⟨bounded, generated⟩⟩

/-- Execution-level preservation of the chronological operational carrier. -/
theorem compileExecution?_located
    {program : GuestProgram} {execution : Machine.EventExecutionTrace} {initialClock : ℕ}
    {compiled : CompiledExecution}
    (generated : compileExecution? program execution initialClock = some compiled) :
    compiled.rows.map CompiledLocatedInstruction.located = execution.locatedTransitions :=
  compileLocatedTransitions?_located ((compileExecution?_eq_some_iff ..).mp generated).2

end SP1Clean.TraceGen

namespace SP1Clean.Execution

open SP1Clean.Soundness.Target

/-- The narrow semantic image on which the native compiler is total and its emitted semantic
events meet the corresponding registry contracts.  This predicate mentions neither a field nor a
Clean witness. -/
def NativeCompilerReady (statementProgram : GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) : Prop :=
  ∃ compiled : TraceGen.CompiledExecution,
    TraceGen.compileExecution? statementProgram execution initialClock = some compiled ∧
      compiled.WellFormed

/-- The common semantic relation already discharges the outer transition projection for the
chronological compiler.  Consequently, compiler success reduces to the one-row event compiler on
the evaluated trace; fetch, decode, image, and route are not separate completeness premises. -/
theorem SupportedCoreShardExecutionValid.compileExecution?_exists_of_instructionEventsReady
    {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p}
    {witness : Machine.CoreShardSemanticWitness} {initialClock : ℕ}
    (valid : SupportedCoreShardExecutionValid statement witness)
    (ordinary : (witness.evaluatedTrace (supportedCoreShardModel (p := p))).AllOrdinary)
    (ready : ∀ located ∈
        (witness.evaluatedTrace (supportedCoreShardModel (p := p))).locatedTransitions,
      ∀ view : SP1Clean.Semantics.SP1TransitionView,
        SP1Clean.Semantics.projectSP1Transition? statement.program located = some view →
          ∀ frontier clock, TraceGen.InstructionEventReady view frontier clock) :
    ∃ compiled,
      TraceGen.compileExecution? statement.program
        (witness.evaluatedTrace (supportedCoreShardModel (p := p))) initialClock =
          some compiled := by
  let execution := witness.evaluatedTrace (supportedCoreShardModel (p := p))
  obtain ⟨-, -, -, -, -, ordinaryTrace, supported, bounded⟩ := valid.evaluatedTrace_facts ordinary
  have statementSupported : ∀ located ∈ execution.locatedTransitions,
      SupportedSP1Transition statement.program located := by
    simpa only [valid.program_eq] using supported.all_of_allOrdinary ordinaryTrace
  apply TraceGen.compileExecution?_exists_of_views bounded
  intro located member
  obtain ⟨view, projected, -⟩ := (statementSupported located member).view
  exact ⟨view, projected, ready located member view projected⟩

end SP1Clean.Execution
