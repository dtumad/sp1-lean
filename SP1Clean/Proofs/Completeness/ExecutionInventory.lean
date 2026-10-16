import SP1Clean.Proofs.Completeness.ExecutionCompiler
import SP1Clean.Proofs.Completeness.MemoryHistory
import SP1Clean.Proofs.Completeness.StateInventory

/-! # Native compiler inventories and capacity

Chronological instruction rows determine register refreshes and Memory boundary records before
physical AIR assembly. The canonical access extractor emits at most three roles per instruction;
each role may add one refresh. These structural facts and the existing ordinary shard limit prove
that the resulting native inventories fit Clean's row-count type. No physical readiness premise
is added to the execution domain. Provider recounting and fixed-table padding need separate bounds.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Semantics

namespace CompiledExecution

/-- The chronological dependent instruction stream retained by the global compiler. -/
def routedEvents (compiled : CompiledExecution) : List RoutedEvent :=
  compiled.rows.map fun row => row.instruction.routed

/-- The single chronological Memory-record stream.  Each scheduled role expands its optional
refresh before the instruction access which consumes it. -/
def memoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.rows.flatMap fun row =>
    MemoryHistoryAccess.ofAccessSchedule row.clock row.instruction.schedule

/-- Instruction-owned history transitions, still in chronological row/role order. -/
def instructionMemoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.rows.flatMap fun row =>
    row.instruction.stamped.map (MemoryHistoryAccess.ofStamped row.clock)

/-- Refresh-owned history transitions, in chronological row/role order. -/
def bumpMemoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.memoryBumps.map MemoryHistoryAccess.ofMemoryBump

@[simp] theorem instructionEvents_eq_ofChronological (compiled : CompiledExecution) :
    compiled.instructionEvents = EventBuckets.ofChronological compiled.routedEvents := rfl

@[simp] theorem memoryHistory_nil :
    (emptyCompiledExecution 0).memoryHistory = [] := rfl

end CompiledExecution

private theorem flatMap_length_le {α β : Type} (items : List α) (expand : α → List β)
    (width : ℕ) (bounded : ∀ item ∈ items, (expand item).length ≤ width) :
    (items.flatMap expand).length ≤ width * items.length := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have head := bounded item List.mem_cons_self
      have tail := ih (fun item member => bounded item (List.mem_cons_of_mem _ member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
      omega

/-- A projected ordinary instruction retains at most the three canonical access roles. -/
theorem compileInstructionEvent?_schedule_length
    {program : Soundness.Target.GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} {frontier : AccessFrontier} {clock : ℕ}
    {compiled : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clock = some compiled) :
    compiled.schedule.accesses.length ≤ 3 := by
  have shape := congrArg List.length (compileInstructionEvent?_stamped_touches generated)
  simp only [CompiledInstructionEvent.stamped, AccessSchedule.stampedTouches,
    List.length_map] at shape
  exact shape.le.trans (instructionAccessPlan_length_le_three
    (compileInstructionEvent?_accessPlan_generated projected generated))

/-- Every row retained by the chronological compiler has the same semantic access bound. -/
theorem compileLocatedTransitions?_schedule_lengths
    {program : Soundness.Target.GuestProgram} {clock : ℕ} {frontier : AccessFrontier}
    {transitions : List Machine.LocatedTransition} {compiled : CompiledExecution}
    (generated : compileLocatedTransitions? program clock frontier transitions = some compiled) :
    ∀ row ∈ compiled.rows, row.instruction.schedule.accesses.length ≤ 3 := by
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
                  intro row member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact compileInstructionEvent?_schedule_length projectionEq instructionEq
                  · exact ih tailEq row member

/-- This bound also holds for the total compiler's empty unsupported result. -/
theorem compileExecution_schedule_lengths (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    ∀ row ∈ (compileExecution program execution initialClock).rows,
      row.instruction.schedule.accesses.length ≤ 3 := by
  cases generated : compileExecution? program execution initialClock with
  | none => simp [compileExecution, generated, emptyCompiledExecution]
  | some compiled =>
      rw [compileExecution_eq_of_some generated]
      exact compileLocatedTransitions?_schedule_lengths
        ((compileExecution?_eq_some_iff ..).mp generated).2

/-- Each access role can create at most one register refresh. -/
theorem CompiledExecution.memoryBumps_length_le (compiled : CompiledExecution)
    (schedules : ∀ row ∈ compiled.rows, row.instruction.schedule.accesses.length ≤ 3) :
    compiled.memoryBumps.length ≤ 3 * compiled.rows.length := by
  apply flatMap_length_le _ _ 3
  intro row member
  exact (List.length_filterMap_le _ _).trans (schedules row member)

/-- The compiler's refresh count is bounded by the original semantic transcript. -/
theorem compileExecution_memoryBumps_length_le (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (compileExecution program execution initialClock).memoryBumps.length ≤ 3 * execution.steps :=
  ((compileExecution program execution initialClock).memoryBumps_length_le
    (compileExecution_schedule_lengths program execution initialClock)).trans
      (Nat.mul_le_mul_left 3 (compileExecution_rows_length_le program execution initialClock))

/-- A scheduled role expands to its instruction access and at most one preceding refresh. -/
theorem MemoryHistoryAccess.ofAccessSchedule_length_le (clock : ℕ) (schedule : AccessSchedule) :
    (MemoryHistoryAccess.ofAccessSchedule clock schedule).length ≤ 2 * schedule.accesses.length := by
  apply flatMap_length_le _ _ 2
  intro access _
  unfold MemoryHistoryAccess.ofScheduledAccess
  cases access.memoryBump? <;> simp

/-- The full chronological Memory history includes refreshes without duplicating other accesses. -/
theorem CompiledExecution.memoryHistory_length_le (compiled : CompiledExecution)
    (schedules : ∀ row ∈ compiled.rows, row.instruction.schedule.accesses.length ≤ 3) :
    compiled.memoryHistory.length ≤ 6 * compiled.rows.length := by
  apply flatMap_length_le _ _ 6
  intro row member
  exact (MemoryHistoryAccess.ofAccessSchedule_length_le _ _).trans
    (Nat.mul_le_mul_left 2 (schedules row member))

/-- The compiler's complete Memory history is bounded by the semantic transcript. -/
theorem compileExecution_memoryHistory_length_le (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (compileExecution program execution initialClock).memoryHistory.length ≤ 6 * execution.steps :=
  ((compileExecution program execution initialClock).memoryHistory_length_le
    (compileExecution_schedule_lengths program execution initialClock)).trans
      (Nat.mul_le_mul_left 6 (compileExecution_rows_length_le program execution initialClock))

/-- Boundary generation emits one row per touched location, never per refresh occurrence. -/
theorem memoryBoundaryEntries_length_le (stream : List MemoryHistoryAccess) :
    (memoryInitialEntries stream).length ≤ stream.length ∧
      (memoryFinalEntries stream).length ≤ stream.length := by
  rw [memoryInitialEntries_length, memoryFinalEntries_length]
  have bounded : (touchedMemoryLocations stream).length ≤ stream.length :=
    (List.dedup_sublist _).length_le.trans (List.length_map _).le
  exact ⟨bounded, bounded⟩

/-- Existing semantic row limits suffice for refresh and both Memory boundary tables. The total
compiler checks that limit; its unsupported and oversized fallback has empty inventories. -/
theorem compileExecution_memory_capacity (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (compileExecution program execution initialClock).memoryBumps.length ≤ UInt64.size ∧
      (memoryInitialEntries (compileExecution program execution initialClock).memoryHistory).length ≤ UInt64.size ∧
      (memoryFinalEntries (compileExecution program execution initialClock).memoryHistory).length ≤ UInt64.size := by
  have schedules := compileExecution_schedule_lengths program execution initialClock
  have refreshBound := (compileExecution program execution initialClock).memoryBumps_length_le schedules
  have historyBound := (compileExecution program execution initialClock).memoryHistory_length_le schedules
  have boundaryBound := memoryBoundaryEntries_length_le
    (compileExecution program execution initialClock).memoryHistory
  have bounded := compileExecution_rows_length_le_limit program execution initialClock
  have limit : 6 * Model.Core.Profile.maxOrdinaryTransitions ≤ UInt64.size := by decide
  unfold Model.Core.Profile.WithinOrdinaryRowLimit at bounded
  omega

/-- The chronological compiler needs at most one State refresh per semantic transition. -/
theorem compileExecution_stateBumps_length_le (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (stateBumpEvents (compileExecution program execution initialClock).routedEvents).length ≤
      execution.steps := by
  apply (stateBumpEvents_length_le _).trans
  rw [CompiledExecution.routedEvents, List.length_map]
  exact compileExecution_rows_length_le program execution initialClock

/-- The checked semantic shard limit also supplies the State table's physical capacity. -/
theorem compileExecution_state_capacity (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (stateBumpEvents (compileExecution program execution initialClock).routedEvents).length ≤
      UInt64.size := by
  apply (stateBumpEvents_length_le _).trans
  rw [CompiledExecution.routedEvents, List.length_map]
  exact (compileExecution_rows_length_le_limit program execution initialClock).trans
    (show Model.Core.Profile.maxOrdinaryTransitions ≤ UInt64.size from by decide)

/-- Exact representability of the inventories used by physical assembly. This proof bundle stores
no additional rows and imposes no condition on semantic execution or circuit validity. -/
structure CompiledExecution.Capacity (compiled : CompiledExecution) : Prop where
  instruction : ∀ id, (compiled.instructionEvents id).length ≤ UInt64.size
  memoryBumps : compiled.memoryBumps.length ≤ UInt64.size
  memoryInitial : (memoryInitialEntries compiled.memoryHistory).length ≤ UInt64.size
  memoryFinal : (memoryFinalEntries compiled.memoryHistory).length ≤ UInt64.size
  stateBumps : (stateBumpEvents compiled.routedEvents).length ≤ UInt64.size

/-- The existing unsupported-input fallback has no physical instruction or provider rows. -/
theorem emptyCompiledExecution_capacity (clock : ℕ) : (emptyCompiledExecution clock).Capacity := by
  constructor <;> intros <;> exact Nat.zero_le _

/-- The total checked compiler always supplies the exact physical capacities. Successful
compilation preserves all input transitions; unsupported inputs use the existing empty result. -/
theorem compileExecution_capacity (program : Soundness.Target.GuestProgram)
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ) :
    (compileExecution program execution initialClock).Capacity := by
  obtain ⟨refreshes, initial, final⟩ := compileExecution_memory_capacity program execution initialClock
  exact ⟨compileExecution_instruction_capacity program execution initialClock, refreshes, initial,
    final, compileExecution_state_capacity program execution initialClock⟩

end SP1Clean.TraceGen
