import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.Proofs.Completeness.InstructionSuccessor
import SP1Clean.FormalModel.ShardNextPC
import SP1Clean.FormalModel.ShardRelease

/-! # Ordinary instruction inputs at actual cuts of a released mixed shard -/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

/-- The arithmetic, upper-immediate and control-flow adapters receive valid events at every
ordinary cut of the released mixed execution. Timestamps are computed from the actual path.
The selected control address and alignment come from normal Sail retirement, and only an
enabled link write uses the released three-limb link condition. -/
theorem releaseAdmissibleExecution_compile_from_prefix {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : ReleaseAdmissibleExecution limits p image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) :
    ∃ current frontier next view row,
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      projectSP1Transition? image.program ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      compileInstructionEvent? view frontier current.clock = some row ∧
      mixedAccessPrefix (policy p image) image.program source.realize events (cut + 1) =
        some (next, row.nextFrontier) ∧
      (∀ touch ∈ row.stamped, touch.previous < touch.current current.clock) ∧
      (∀ bump ∈ row.memoryBumps, bump.WellFormed) ∧
      (view.chipId ∈ [.add, .sub, .subw, .mul, .divRem, .aluX0, .addi, .addw, .bitwise, .lt,
          .shiftLeft, .shiftRight, .jal, .jalr, .branch, .uType] → row.routed.id.Valid row.routed.event) := by
  obtain ⟨current, frontier, next, view, row, before, projected, made, after, times, bumps, arithmetic⟩ :=
    admissibleExecution_compile_from_prefix execution.1 ordinary
  refine ⟨current, frontier, next, view, row, before, projected, made, after, times, bumps, ?_⟩
  intro family
  change view.chipId ∈ [.add, .sub, .subw, .mul, .divRem, .aluX0, .addi, .addw, .bitwise,
    .lt, .shiftLeft, .shiftRight] ++ [.jal, .jalr, .branch, .uType] at family
  rcases List.mem_append.mp family with arith | control
  · exact arithmetic arith
  obtain ⟨s, f, replay, before', bounded⟩ := admissibleExecution_mixedAccessPrefix execution.1 cut
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (before'.symm.trans before))
  obtain ⟨t, g, nextCut, after', _⟩ := admissibleExecution_mixedAccessPrefix execution.1 (cut + 1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (after'.symm.trans after))
  obtain ⟨current', next', replay', step⟩ := execution.1.1.2.step_at ordinary
  cases Option.some.inj (replay'.symm.trans replay)
  have atNext := nextCut
  rw [executionTrajectory_succ _ _ _ _ ordinary, replay, Option.bind_some, step.replay] at atNext
  cases Option.some.inj atNext
  have phase := (execution.1.2.1 cut _ .ordinary ordinary replay).1
  apply compileInstructionEvent?_control_valid_of_targets projected made control phase bounded
  have frame := execution.1.1.frame_prefix replay
  cases step with
  | ordinary _ _ normal permitted =>
    exact compileInstructionEvent?_release_targets frame.1 frame.2.1 permitted normal projected made
      (fun _ addr => Executes.pc_at execution.1 nextCut addr) (execution.2 cut _ ordinary replay)

end SP1Clean.TraceGen
