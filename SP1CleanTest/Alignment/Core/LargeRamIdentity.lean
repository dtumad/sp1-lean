import SP1Clean.FormalModel.ShardRelease
import SP1Clean.Math.SP1Field

/-! # A native release identity with a large finite RAM boundary

The committed RV64 store instruction has four identical bytes. A finite region of that same
byte supplies its ROM and all of the live RAM. The example proves its size symbolically and
needs no allocation of a large array during checking.
-/

namespace SP1CleanTest.FixedRamCapacity
open SP1Clean SP1Clean.Semantics SP1Clean.FormalModel.Shard SP1Clean.Soundness.Target
open LeanRV64D

private def image : ProgramImage := ⟨[(65536, 0x23232323)], 65536, []⟩

private def memory (count : ℕ) : ByteMemory :=
  ⟨(List.range count).map fun i => (65536 + i, 0x23)⟩

private theorem readAt {count i : ℕ} (inside : i < count) :
    (memory count).read (65536 + i) = 0x23 := by
  apply ByteMemory.read_eq_of_mem
  · exact List.mem_map.mpr ⟨i, List.mem_range.mpr inside, rfl⟩
  · intro entry member _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl

private theorem supportCount (count : ℕ) (bounded : 65536 + count ≤ NativeLayout.sailMemory.upper) :
    ((memory count).supportBelow NativeLayout.sailMemory.upper).card = count := by
  let addresses := (Finset.range count).image (fun i : ℕ => 65536 + i)
  have exactSupport : (memory count).supportBelow NativeLayout.sailMemory.upper = addresses := by
    ext address
    rw [ByteMemory.mem_supportBelow]
    constructor
    · rintro ⟨_, live⟩
      by_contra absent
      apply live
      apply ByteMemory.read_eq_zero_of_absent
      intro entry member equal
      obtain ⟨i, inside, rfl⟩ := List.mem_map.mp member
      exact absent (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (List.mem_range.mp inside), equal⟩)
    · intro member
      obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
      have h := Finset.mem_range.mp inside
      exact ⟨by omega, by rw [readAt h]; decide⟩
  have injective : Function.Injective (fun i : ℕ => 65536 + i) := fun _ _ equal => Nat.add_left_cancel equal
  rw [exactSupport]
  exact (Finset.card_image_of_injective _ injective).trans (Finset.card_range count)

private def source (count : ℕ) : ExecutionSnapshot :=
  ⟨{ registers := (configuredState 65536).regs, memory := memory count }, {}, 1⟩

private theorem pc (count : ℕ) : (source count).pc = 65536 := by
  change ((configuredState 65536).regs.get? Register.PC).getD 0 = _
  rw [cfgState_pc]
  rfl

private theorem sourceValid (count : ℕ) (enough : 4 ≤ count) : ExecutionSourceValid image (source count) := by
  refine ⟨⟨by decide, by decide, SailSnapshot.memorySnapshot_valid _, ?_⟩, cfgState_configured _,
    (by decide : 1 < 2 ^ 48), by rw [pc]; decide⟩
  intro entry member index
  obtain rfl : entry = (65536, 0x23232323) := List.mem_singleton.mp member
  change (memory count).read (65536 + index) = _
  rw [readAt (by have := index.isLt; omega)]
  fin_cases index <;> decide

private theorem fits (count : ℕ) (cost : count + 125 ≤ SP1Prime - 1)
    (support : ((memory count).supportBelow NativeLayout.sailMemory.upper).card = count) :
    (source count).realize.resources.Fits (ResourceLimits.native SP1Prime) := by
  rw [ExecutionSnapshot.resources_realize]
  intro kind
  cases kind with
  | boundaryBytes =>
    change ((memory count).supportBelow NativeLayout.sailMemory.upper).card +
      ({} : HostState).payloadCost + 8 + 0 ≤ SP1Prime - 1
    rw [support]
    exact cost
  | _ => exact Nat.zero_le _

/-- An empty execution with exactly 2^29 live RAM bytes meets every clause of the native
release statement, including both boundary budgets, commitment declarations and jump links. -/
theorem empty_large_ram :
    ∃ image source commitments,
      ReleaseStatementExecution (ResourceLimits.native SP1Prime) SP1Prime commitments image source source [] ∧
      (source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card = 2 ^ 29 := by
  let count : ℕ := 2 ^ 29
  have support := supportCount count (by decide)
  have bounded := fits count (by decide) support
  let commitments : CommitmentStatement := ⟨Vector.replicate 8 0, Vector.replicate 8 0, false, false⟩
  refine ⟨image, source count, commitments, ?_, support⟩
  refine ⟨⟨⟨⟨sourceValid count (by decide), .nil _⟩, ExecutionPath.encoded_nil, ResourceUsage.zero_fits _,
    bounded, bounded, (by decide : 1 < 2 ^ 48), ?_⟩, ExecutionPath.releaseLinks_of_no_ordinary (by simp)⟩,
    by decide, CommitmentStatement.matches_nil _⟩
  rw [pc]
  decide

end SP1CleanTest.FixedRamCapacity
