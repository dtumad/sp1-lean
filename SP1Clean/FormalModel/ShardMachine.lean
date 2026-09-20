import Machine.Core.Path
import SP1Clean.FormalModel.Shard

/-! # The SP1 shard as a labeled machine

`sp1Machine` presents the complete-state execution step of a checked image as a
`Machine.LabeledMachine`: states are `ExecutionState`, labels are `ExecutionEvent`, steps are
`ExecutionStep` at the native host policy, and a stopped host is terminal. Its paths are the
existing `ExecutionPath` (`executionPath_iff_path`), so the generic path algebra and PolyFun view
apply to the shard contract with no new execution carrier: `Executes` is source validity plus a
machine path between the realized snapshots (`executes_iff`).
-/

namespace SP1Clean.FormalModel.Shard

open Model.Core Machine

/-- The full-state SP1 step relation of a checked image as a labeled machine. -/
def sp1Machine (characteristic : ℕ) (image : ProgramImage) (valid : image.Valid) :
    _root_.Machine.LabeledMachine where
  State := ExecutionState
  Event := ExecutionEvent
  Step := ExecutionStep (policy characteristic image) (image.toGuestProgram valid)
  Terminal state := state.host.exitCode ≠ none
  terminal_stuck := fun halted => ExecutionStep.not_of_halted halted

variable {characteristic : ℕ} {image : ProgramImage} {valid : image.Valid}

/-- Every shard path is a labeled-machine path. -/
theorem path_of_executionPath {source target : ExecutionState} {events : List ExecutionEvent} :
    ExecutionPath (policy characteristic image) (image.toGuestProgram valid) source events target →
      _root_.Machine.Path (sp1Machine characteristic image valid) source events target
  | .nil _ => .nil _
  | .cons step rest => .cons step (path_of_executionPath rest)

/-- Every labeled-machine path is a shard path. -/
theorem executionPath_of_path {source target : ExecutionState} {events : List ExecutionEvent} :
    _root_.Machine.Path (sp1Machine characteristic image valid) source events target →
      ExecutionPath (policy characteristic image) (image.toGuestProgram valid) source events target
  | .nil _ => .nil _
  | .cons step rest => .cons step (executionPath_of_path rest)

/-- Shard paths are exactly labeled-machine paths. -/
theorem executionPath_iff_path {source target : ExecutionState} {events : List ExecutionEvent} :
    ExecutionPath (policy characteristic image) (image.toGuestProgram valid) source events target ↔
      _root_.Machine.Path (sp1Machine characteristic image valid) source events target :=
  ⟨path_of_executionPath, executionPath_of_path⟩

/-- Counted shard execution is counted machine reachability. -/
theorem executionSegment_iff_segment {source target : ExecutionState} {steps : ℕ} :
    ExecutionSegment (policy characteristic image) (image.toGuestProgram valid) source steps
        target ↔
      _root_.Machine.Segment (sp1Machine characteristic image valid) source steps target := by
  constructor
  · rintro ⟨events, length, path⟩
    exact ⟨events, length, path_of_executionPath path⟩
  · rintro ⟨events, length, path⟩
    exact ⟨events, length, executionPath_of_path path⟩

/-- `Executes` is source validity plus a machine path between the realized snapshots. -/
theorem executes_iff {source target : ExecutionSnapshot} {events : List ExecutionEvent} :
    Executes characteristic image source target events ↔
      ExecutionSourceValid image source ∧
        _root_.Machine.Path (sp1Machine characteristic image valid) source.realize events target.realize := by
  constructor
  · rintro ⟨sourceValid, path⟩
    exact ⟨sourceValid, executionPath_iff_path.mp path⟩
  · rintro ⟨sourceValid, path⟩
    exact ⟨sourceValid, executionPath_iff_path.mpr path⟩

end SP1Clean.FormalModel.Shard
