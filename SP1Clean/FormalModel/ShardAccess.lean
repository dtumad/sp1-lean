import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.Semantics.Execution.ExecutionAccess

/-! # Access projection at every admissible ordinary occurrence

Both source and target of each instruction are the actual complete path states. Configuration,
ROM and byte availability are derived independently from Sail/host preservation. The conclusion
uses the same transition view and access plan consumed by the deterministic compiler.
-/

namespace SP1Clean.FormalModel.Shard
open Model.Core Machine Semantics

/-- Native admissibility preserves the exact complete byte domain at every actual cut. -/
theorem AdmissibleExecution.memory_domain_prefix {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) image.program
      source.realize events cut = some current) (address : ℕ) :
    (current.sail.mem.get? address).isSome ↔ address < NativeLayout.sailMemory.upper := by
  obtain ⟨⟨valid, path⟩, encoded, _⟩ := execution
  rw [image.program_eq valid.1.1] at path encoded replay
  exact path.memory_domain_prefix valid.1.1 encoded (fun _ selected => selected) (by rfl)
    valid.configured valid.romLoaded replay address

/-- Every ordinary position in the capstone domain has a successful canonical access projection. -/
theorem AdmissibleExecution.project_at {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) :
    ∃ current next view plan,
      executionTrajectory (policy characteristic image) image.program
        source.realize events cut = some current ∧
      ExecutionStep (policy characteristic image) image.program current .ordinary next ∧
      projectSP1Transition? image.program
        ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      view.accessPlan? = some plan ∧ plan.WellFormed ∧ plan.length ≤ 3 := by
  obtain ⟨current, next, replay, step⟩ := execution.1.2.step_at ordinary
  have frame := execution.1.frame_prefix replay
  have encoded := execution.2.1 cut current .ordinary ordinary replay
  obtain ⟨view, plan, projected, generated, wellFormed, length⟩ :=
    step.project_ordinary frame.1 frame.2.1 (encoded.2 rfl)
      (execution.1.memory_present_prefix replay)
  exact ⟨current, next, view, plan, replay, step, projected, generated, wellFormed, length⟩

end SP1Clean.FormalModel.Shard
