import SP1Clean.Model.Core.InstructionFetch
import SP1Clean.FormalModel.Shard

/-! # Authenticated ordinary fetch and boundaries without a successor instruction

The checked boundary authenticates an ordinary JALR word in actual Sail memory. Corrupting any
of its four bytes fails source validation. A valid empty segment can nevertheless have a PC
outside the finite ROM: source validity does not invent a fetch obligation at an unused boundary.
-/

namespace SP1CleanTest.Core.InstructionFetch

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D.Defs LeanRV64D.Functions

private def image : ProgramImage := ⟨[(65536, 0x00008067)], 65536, []⟩

private def source : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x1 65545)
            memory := image.initialMemory }
  host := {}
  clock := 17

private theorem source_valid : ExecutionSourceValid image source := by
  apply (checkExecutionSource_iff image source).mp
  native_decide

/-- The official Sail fetch observes the authenticated JALR word, without a chip witness. -/
theorem ordinaryFetch : (fetch ()).run source.sail.realize =
    .ok (FetchResult.F_Base 0x00008067) source.sail.realize :=
  source_valid.fetch_eq (by native_decide)

/-- Every byte of an ordinary instruction, including zero bytes, is authenticated. -/
theorem rejectsCorruptedCode :
    (List.range 4).map (fun offset => checkExecutionSource image
      { source with sail.memory := source.sail.memory.write (65536 + offset) 255 }) =
      [false, false, false, false] := by
  native_decide

private def unusedBoundary : ExecutionSnapshot :=
  { source with sail.registers := source.sail.registers.insert .PC 65544 }

private theorem unused_valid : ExecutionSourceValid image unusedBoundary := by
  apply (checkExecutionSource_iff image unusedBoundary).mp
  native_decide

/-- Empty segments need no next instruction, even when the host remains running. -/
theorem identityWithoutFetch (characteristic : ℕ) :
    (image.toGuestProgram unused_valid.1.1).fetchWord unusedBoundary.pc = none ∧
      FormalModel.Shard.Executes characteristic image unusedBoundary unusedBoundary [] := by
  refine ⟨by native_decide, ?_⟩
  exact FormalModel.Shard.Executes.nil_iff.mpr
    ⟨unused_valid, (ExecutionSnapshot.equivalent_iff _ _).mpr rfl⟩

end SP1CleanTest.Core.InstructionFetch
