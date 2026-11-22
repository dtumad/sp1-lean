import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.Proofs.Completeness.InstructionSuccessor
import SP1Clean.FormalModel.ShardNextPC
import SP1Clean.FormalModel.ShardRelease

/-! # Ordinary instruction inputs at actual cuts of a released mixed shard -/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

private theorem projected_memory_encoding {program : GuestProgram} {located : LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) (configured : SailConfigured located.source)
    (encoded : ordinaryEncodedAt program located.source) : instructionMemoryEncoded located.source.get_reg? view.decoded := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, _, _, access⟩ := encoded
  have observed : decodeLocated? program located = some decoded := decodeLocated?_eq_some_of atPc fetched (decode _ configured)
  have same := (projectSP1Transition?_components projected).2.2.1
  cases Option.some.inj (observed.symm.trans same)
  exact access

/-- All twenty-five ordinary adapters receive valid events at every ordinary cut of the released
mixed execution. The canonical row uses the replayed register and RAM timestamps. The decoded
memory width and actual base register determine its checked span and alignment.
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
      row.routed.id.Valid row.routed.event := by
  obtain ⟨current, frontier, next, view, row, before, projected, made, after, times, bumps, arithmetic⟩ :=
    admissibleExecution_compile_from_prefix execution.1 ordinary
  refine ⟨current, frontier, next, view, row, before, projected, made, after, times, bumps, ?_⟩
  have families (id : InstructionChipId) :
      id ∈ [.add, .sub, .subw, .mul, .divRem, .aluX0, .addi, .addw, .bitwise, .lt, .shiftLeft, .shiftRight] ++
        ([.jal, .jalr, .branch, .uType] ++ [.loadByte, .loadHalf, .loadWord, .loadDouble, .loadX0,
          .storeByte, .storeHalf, .storeWord, .storeDouble]) := by
    cases id <;> decide
  rcases List.mem_append.mp (families view.chipId) with arith | remaining
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
  have encoded := execution.1.2.1 cut _ .ordinary ordinary replay
  have frame := execution.1.1.frame_prefix replay
  rcases List.mem_append.mp remaining with control | memory
  · apply compileInstructionEvent?_control_valid_of_targets projected made control encoded.1 bounded
    cases step with
    | ordinary _ _ normal permitted =>
      exact compileInstructionEvent?_release_targets frame.1 frame.2.1 permitted normal projected made
        (fun _ addr => Executes.pc_at execution.1 nextCut addr) (execution.2 cut _ ordinary replay)
  · have access := projected_memory_encoding projected frame.1 (encoded.2 rfl)
    have clock := execution.1.1.2.clock_at ordinary replay
    have final : target.clock < 2 ^ 48 := execution.1.2.2.2.2.2.1
    change _ + 8 ≤ target.clock at clock
    exact compileInstructionEvent?_memory_valid projected made memory access encoded.1 (by omega) bounded

end SP1Clean.TraceGen
