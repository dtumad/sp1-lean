import PolyFun.PFunctor.Dynamical.Trace
import SP1Clean.FormalModel.Shard
/-! # The SP1 shard as a PolyFun labeled machine

`sp1Machine` bundles the existing PolyFun view of an image's complete-state execution step
(`executionSystem`/`executionEventMap`, `Semantics/Execution/ExecutionPath.lean`) as a
`PFunctor.DynSystem.Labeled` machine over the image's committed program. Its traces are the existing
`ExecutionPath` (`trace_iff_executionPath`, from the orbit correspondence proved beside the system),
so the generic realization statement applies to the shard contract with no new execution carrier:
`Executes` is source validity plus a machine trace between the realized snapshots (`executes_iff`).
An invalid image commits no instruction, so its machine has no step.
-/

namespace SP1Clean.FormalModel.Shard

open Semantics Machine PFunctor PFunctor.DynSystem

/-- The full-state SP1 step relation of an image's committed program as a labeled machine. -/
def sp1Machine (characteristic : ℕ) (image : ProgramImage) :
    Labeled (executionInterface (policy characteristic image) image.program) where
  State := ExecutionState
  toDynSystem := executionSystem (policy characteristic image) image.program
  Event := ExecutionEvent
  event := executionEventMap (policy characteristic image) image.program

variable {characteristic : ℕ} {image : ProgramImage}

/-- Machine traces are exactly shard paths. -/
theorem trace_iff_executionPath {source target : ExecutionState} {events : List ExecutionEvent} :
    (sp1Machine characteristic image).Trace source events target ↔
      ExecutionPath (policy characteristic image) image.program source events target := by
  constructor
  · rintro ⟨_, orbit, rfl, rfl⟩
    exact executionPath_of_prefix orbit
  · intro path
    obtain ⟨orbit, endpoint, labels⟩ := path.exists_prefix
    exact ⟨_, orbit, labels, endpoint⟩

/-- `Executes` is source validity together with a machine trace. -/
theorem executes_iff {source target : ExecutionSnapshot} {events : List ExecutionEvent} :
    Executes characteristic image source target events ↔
      ExecutionSourceValid image source ∧
        (sp1Machine characteristic image).Trace source.realize events target.realize :=
  and_congr_right fun _ => trace_iff_executionPath.symm

end SP1Clean.FormalModel.Shard
