import ToPolyFun.Dynamical.Labeled
import SP1Clean.FormalModel.Shard
/-! # The SP1 shard as a PolyFun labeled machine

`sp1Machine` bundles the existing PolyFun view of a checked image's complete-state execution step
(`executionSystem`/`executionEventMap`, `Model/Core/ExecutionPath.lean`) as a
`PFunctor.DynSystem.Labeled` machine. Its traces are the existing `ExecutionPath`
(`trace_iff_executionPath`, from the orbit correspondence proved beside the system), so the
generic realization statement applies to the shard contract with no new execution carrier:
`Executes` is source validity plus a machine trace between the realized snapshots
(`executes_iff`).
-/

namespace SP1Clean.FormalModel.Shard

open Model.Core Machine PFunctor PFunctor.DynSystem

/-- The full-state SP1 step relation of a checked image as a labeled machine. -/
def sp1Machine (characteristic : ℕ) (image : ProgramImage) (valid : image.Valid) :
    Labeled (executionInterface (policy characteristic image) (image.toGuestProgram valid)) where
  State := ExecutionState
  toDynSystem := executionSystem (policy characteristic image) (image.toGuestProgram valid)
  Event := ExecutionEvent
  event := executionEventMap (policy characteristic image) (image.toGuestProgram valid)

variable {characteristic : ℕ} {image : ProgramImage} {valid : image.Valid}

/-- Machine traces are exactly shard paths. -/
theorem trace_iff_executionPath {source target : ExecutionState} {events : List ExecutionEvent} :
    (sp1Machine characteristic image valid).Trace source events target ↔
      ExecutionPath (policy characteristic image) (image.toGuestProgram valid) source events
        target := by
  constructor
  · rintro ⟨_, orbit, rfl, rfl⟩
    exact executionPath_of_prefix orbit
  · intro path
    obtain ⟨orbit, endpoint, labels⟩ := path.exists_prefix
    exact ⟨_, orbit, labels, endpoint⟩

/-- `Executes` is source validity plus a machine trace between the realized snapshots. -/
theorem executes_iff {source target : ExecutionSnapshot} {events : List ExecutionEvent} :
    Executes characteristic image source target events ↔
      ExecutionSourceValid image source ∧
        (sp1Machine characteristic image valid).Trace source.realize events target.realize := by
  constructor
  · rintro ⟨sourceValid, path⟩
    exact ⟨sourceValid, trace_iff_executionPath.mpr path⟩
  · rintro ⟨sourceValid, trace⟩
    exact ⟨sourceValid, trace_iff_executionPath.mp trace⟩

end SP1Clean.FormalModel.Shard
