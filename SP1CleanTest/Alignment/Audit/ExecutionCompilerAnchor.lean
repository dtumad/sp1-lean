import SP1CleanTest.Alignment.Support.AnchorShard
import SP1Clean.Proofs.Completeness.ExecutionCompiler
import SP1Clean.Proofs.Completeness.InstructionEvent

/-! # The chronological compiler on the anchor self-jump

The one official-Sail `JAL x0, 0` step of `AnchorShard` exercises the event and execution compilers
on one concrete non-padding row. Every compiler result for the anchored input routes the exact JAL
circuit event, and the common semantic witness recovers the execution. These builders are the
starting material for the mixed compiler (#12 C9/C10); this file closes no completeness obligation.
-/

open LeanRV64D
open LeanRV64D.Functions

namespace SP1Clean.Audit.ExecutionCompilerAnchor

open SP1Clean.Execution SP1Clean.Soundness SP1Clean.TraceGen
open SP1Clean.Audit.AnchorShard
open SP1Clean.Soundness.Target

/-- The executor event for the committed self-loop.  Its sole register access is x0's prior record
at clock `0`; the JAL row touches it at micro-time `1 + 4 = 5` and writes the architectural zero
back. -/
def activeEvent : JTypeEvent where
  clk := 1
  pc := 65536
  opcode := 46
  opA := 0
  immB := 0
  immC := 0
  prevA := 0
  prevTsA := 0

theorem activeEvent_wellFormed : activeEvent.WellFormedJal := by
  simp only [activeEvent]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_,
    by norm_num⟩
  intro _
  rfl

theorem activeEvent_targets : activeEvent.JalTargets := by
  norm_num [activeEvent, JTypeEvent.JalTargets, JTypeEvent.jalTarget]

/-- The self-jump has the single immutable `x0` access expected by the J-type compiler. -/
theorem activeView_accessPlan :
    activeView.accessPlan? = some
      [{ slot := .opA, loc := .reg 0#5, pulled := 0#64, pushed := 0#64 }] := by
  rfl

/-- The one-row event compiler succeeds for every incoming access frontier and row clock. -/
theorem activeView_instructionEventReady (frontier : SP1Clean.Semantics.AccessFrontier)
    (clock : ℕ) : InstructionEventReady activeView frontier clock :=
  instructionEventReady_of_projection activeExecution_projected activeView_accessPlan frontier clock

/-- Every successful compiler result for the anchored input routes the exact circuit event. -/
theorem activeView_compiled_event
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? activeView SP1Clean.Semantics.AccessFrontier.initial 1 =
      some result) :
    result.routed = ⟨.jal, activeEvent⟩ := by
  unfold compileInstructionEvent? at generated
  rw [activeView_accessPlan] at generated
  injection generated with resultEq
  cases resultEq
  rfl

/-- The anchored input has a successful compiler result carrying the exact circuit event. -/
theorem activeView_compiled_event_exists :
    ∃ result,
      compileInstructionEvent? activeView SP1Clean.Semantics.AccessFrontier.initial 1 =
        some result ∧
      result.routed = ⟨.jal, activeEvent⟩ := by
  obtain ⟨result, generated⟩ :=
    instructionEventReady_iff.mp
      (activeView_instructionEventReady SP1Clean.Semantics.AccessFrontier.initial 1)
  exact ⟨result, generated, activeView_compiled_event generated⟩

/-- The optional chronological compiler succeeds on the active semantic execution. -/
theorem activeExecution_compileExecution?_exists :
    ∃ compiled, compileExecution? anchorProgram activeExecution 1 = some compiled := by
  apply compileExecution?_exists_of_views
    (by change 1 ≤ Model.Core.Profile.maxOrdinaryTransitions; decide)
  intro located member
  rw [activeExecution_locatedTransitions, List.mem_singleton] at member
  subst located
  exact ⟨activeView, activeExecution_projected, activeView_instructionEventReady⟩

/-- The successful deterministic compiler emits exactly one chronological instruction record. -/
theorem activeExecution_compiled_rows_length :
    (compileExecution anchorProgram activeExecution 1).rows.length = 1 := by
  obtain ⟨compiled, generated⟩ := activeExecution_compileExecution?_exists
  rw [compileExecution_eq_of_some generated]
  exact compileLocatedTransitions?_rows_length
    ((compileExecution?_eq_some_iff ..).mp generated).2

/-- The nonempty execution embedded in the one common semantic witness. -/
noncomputable def activeSemanticWitness : Machine.CoreShardSemanticWitness :=
  Machine.CoreShardSemanticWitness.ofOrdinaryTrace anchorProgram ⟨[]⟩ activeExecution

/-- Evaluating the common semantic witness recovers the exact nonempty execution. -/
theorem activeSemanticWitness_trace :
    activeSemanticWitness.trace? (supportedCoreShardModel (p := SP1Prime)) =
      some activeExecution := by
  exact Machine.CoreShardSemanticWitness.trace?_ofOrdinaryTrace
    (supportedCoreShardModel (p := SP1Prime)) anchorProgram ⟨[]⟩ activeExecution
    activeExecution_valid activeExecution_allOrdinary


end SP1Clean.Audit.ExecutionCompilerAnchor
