import SP1Clean.FormalModel.ShardRelease
import SP1Clean.Math.SP1Field
import SP1Clean.Semantics.Memory.MemoryIntervals

/-! # Native release identities with large finite RAM boundaries

The committed RV64 store instruction occupies four identical bytes. Constant and alternating
regions in the same valid release profile give different numbers of neighboring byte changes.
All bounds are proved on finite ranges without evaluating the large memories.
-/

namespace SP1CleanTest.FixedRamCapacity
open SP1Clean SP1Clean.Semantics SP1Clean.FormalModel.Shard SP1Clean.Soundness.Target
open LeanRV64D

private def image : ProgramImage := ⟨[(65536, 0x23232323)], 65536, []⟩

private def memory (count : ℕ) (byte : ℕ → BitVec 8) : ByteMemory :=
  ⟨(List.range count).map fun i => (65536 + i, byte i)⟩

private theorem readAt {count i : ℕ} {byte : ℕ → BitVec 8} (inside : i < count) :
    (memory count byte).read (65536 + i) = byte i := by
  apply ByteMemory.read_eq_of_mem
  · exact List.mem_map.mpr ⟨i, List.mem_range.mpr inside, rfl⟩
  · intro entry member equal
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp member
    exact congrArg byte (Nat.add_left_cancel equal)

private theorem readOutside {count address : ℕ} {byte : ℕ → BitVec 8}
    (outside : address < 65536 ∨ 65536 + count ≤ address) : (memory count byte).read address = 0 := by
  apply ByteMemory.read_eq_zero_of_absent
  intro entry member equal
  obtain ⟨i, inside, rfl⟩ := List.mem_map.mp member
  have hi := List.mem_range.mp inside
  change 65536 + i = address at equal
  omega

private theorem supportCount (count : ℕ) (byte : ℕ → BitVec 8) (live : ∀ i, byte i ≠ 0)
    (bounded : 65536 + count ≤ NativeLayout.sailMemory.upper) :
    ((memory count byte).supportBelow NativeLayout.sailMemory.upper).card = count := by
  let addresses := (Finset.range count).image (fun i : ℕ => 65536 + i)
  have exactSupport : (memory count byte).supportBelow NativeLayout.sailMemory.upper = addresses := by
    ext address
    rw [ByteMemory.mem_supportBelow]
    constructor
    · rintro ⟨_, nonzero⟩
      by_cases inside : 65536 ≤ address ∧ address < 65536 + count
      · exact Finset.mem_image.mpr ⟨address - 65536, Finset.mem_range.mpr (by omega), by omega⟩
      · exact (nonzero (readOutside (by omega))).elim
    · intro member
      obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
      have h := Finset.mem_range.mp inside
      exact ⟨by omega, by rw [readAt h]; exact live i⟩
  rw [exactSupport, Finset.card_image_of_injective _ (fun _ _ => Nat.add_left_cancel), Finset.card_range]

private def source (count : ℕ) (byte : ℕ → BitVec 8) : ExecutionSnapshot :=
  ⟨{ registers := (configuredState 65536).regs, memory := memory count byte }, {}, 1⟩

private theorem pc (count : ℕ) (byte : ℕ → BitVec 8) : (source count byte).pc = 65536 := by
  change ((configuredState 65536).regs.get? Register.PC).getD 0 = _
  rw [cfgState_pc]
  rfl

private theorem sourceValid {count : ℕ} {byte : ℕ → BitVec 8}
    (enough : 4 ≤ count) (rom : ∀ i < 4, byte i = 0x23) : ExecutionSourceValid image (source count byte) := by
  refine ⟨⟨by decide, by decide, SailSnapshot.memorySnapshot_valid _, ?_⟩, cfgState_configured _,
    (by decide : 1 < 2 ^ 48), by rw [pc]; decide⟩
  intro entry member index
  obtain rfl : entry = (65536, 0x23232323) := List.mem_singleton.mp member
  change (memory count byte).read (65536 + index) = _
  rw [readAt (by have := index.isLt; omega), rom index index.isLt]
  fin_cases index <;> decide

private theorem fits {count : ℕ} {byte : ℕ → BitVec 8} (cost : count + 125 ≤ SP1Prime - 1)
    (support : ((memory count byte).supportBelow NativeLayout.sailMemory.upper).card = count) :
    (source count byte).realize.resources.Fits (ResourceLimits.native SP1Prime) := by
  rw [ExecutionSnapshot.resources_realize]
  intro kind
  cases kind with
  | boundaryBytes =>
    change ((memory count byte).supportBelow NativeLayout.sailMemory.upper).card +
      ({} : HostState).payloadCost + 8 + 0 ≤ SP1Prime - 1
    rw [support]
    exact cost
  | _ => exact Nat.zero_le _

private def commitments : CommitmentStatement := ⟨Vector.replicate 8 0, Vector.replicate 8 0, false, false⟩

private theorem release {count : ℕ} {byte : ℕ → BitVec 8} (enough : 4 ≤ count)
    (rom : ∀ i < 4, byte i = 0x23) (cost : count + 125 ≤ SP1Prime - 1)
    (support : ((memory count byte).supportBelow NativeLayout.sailMemory.upper).card = count) :
    ReleaseStatementExecution (ResourceLimits.native SP1Prime) SP1Prime commitments image
      (source count byte) (source count byte) [] := by
  have bounded := fits cost support
  refine ⟨⟨⟨⟨sourceValid enough rom, .nil _⟩, ExecutionPath.encoded_nil, ResourceUsage.zero_fits _,
    bounded, bounded, (by decide : 1 < 2 ^ 48), ?_⟩, ExecutionPath.releaseLinks_of_no_ordinary (by simp)⟩,
    by decide, CommitmentStatement.matches_nil _⟩
  rw [pc]
  decide

private theorem constantRead (count address : ℕ) :
    (memory count (fun _ => 0x23)).read address =
      if 65536 ≤ address ∧ address < 65536 + count then 0x23 else 0 := by
  split
  next inside =>
    have value := readAt (byte := fun _ => 0x23) (show address - 65536 < count by omega)
    rwa [show 65536 + (address - 65536) = address by omega] at value
  next outside => exact readOutside (by omega)

private def alternating (i : ℕ) : BitVec 8 :=
  if i < 4 ∨ i % 2 = 0 then 0x23 else 0x24

private theorem alternating_ne (i : ℕ) : alternating (4 + i) ≠ alternating (5 + i) := by
  by_cases even : (4 + i) % 2 = 0
  · have odd : (5 + i) % 2 ≠ 0 := by omega
    simp [alternating, even, odd]
    omega
  · have next : (5 + i) % 2 = 0 := by omega
    simp [alternating, even, next]

private theorem constantChanges {count limit : ℕ} (hl : 65536 + count < limit) (hc : 0 < count) :
    ((memory count (fun _ => 0x23)).changePoints limit).card = 2 := by
  have positions : (memory count (fun _ => 0x23)).changePoints limit = {65536, 65536 + count} := by
    ext a
    rw [ByteMemory.mem_changePoints]
    simp only [Finset.mem_insert, Finset.mem_singleton, constantRead]
    split_ifs <;> simp_all <;> omega
  rw [positions, Finset.card_insert_of_notMem, Finset.card_singleton]
  simpa using (show 65536 ≠ 65536 + count by omega)

private theorem alternatingChanges (n : ℕ) {limit : ℕ} (bounded : 65536 + (4 + (n + 2)) ≤ limit) :
    n < ((memory (4 + (n + 2)) alternating).changePoints limit).card := by
  let addresses := (Finset.range (n + 1)).image (fun i => 65536 + (5 + i))
  have subset : addresses ⊆ (memory (4 + (n + 2)) alternating).changePoints limit := by
    intro address member
    obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
    have hi := Finset.mem_range.mp inside
    apply (ByteMemory.mem_changePoints ..).mpr
    refine ⟨by omega, by omega, ?_⟩
    rw [show 65536 + (5 + i) - 1 = 65536 + (4 + i) by omega, readAt (by omega), readAt (by omega)]
    exact alternating_ne i
  have injective : Function.Injective (fun i : ℕ => 65536 + (5 + i)) := fun _ _ h =>
    Nat.add_left_cancel (Nat.add_left_cancel h)
  have size : addresses.card = n + 1 := (Finset.card_image_of_injective _ injective).trans (Finset.card_range _)
  have lower := Finset.card_le_card subset
  omega

/-- The constant region occupies 2^29 live bytes, although its entire memory function
changes only twice in the native address window. -/
theorem empty_large_ram :
    ∃ image source commitments,
      ReleaseStatementExecution (ResourceLimits.native SP1Prime) SP1Prime commitments image source source [] ∧
      (source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card = 2 ^ 29 ∧
      (source.sail.memory.changePoints NativeLayout.sailMemory.upper).card = 2 := by
  let count : ℕ := 2 ^ 29
  have support := supportCount count (fun _ => 0x23) (fun _ => by decide) (by decide)
  exact ⟨image, source count _, commitments, release (by decide) (by simp) (by decide) support,
    support, constantChanges (show 65536 + count < NativeLayout.sailMemory.upper by decide) (by decide)⟩

/-- Four equal ROM bytes followed by 2^30 + 2 alternating nonzero bytes fit the native
release budget. More than 2^30 boundaries separate unequal neighboring bytes. -/
theorem empty_alternating_ram :
    ∃ image source commitments,
      ReleaseStatementExecution (ResourceLimits.native SP1Prime) SP1Prime commitments image source source [] ∧
      2 ^ 30 < (source.sail.memory.changePoints NativeLayout.sailMemory.upper).card := by
  let count : ℕ := 4 + (2 ^ 30 + 2)
  have live (i : ℕ) : alternating i ≠ 0 := by unfold alternating; split <;> decide
  have rom (i : ℕ) (hi : i < 4) : alternating i = 0x23 := by simp [alternating, hi]
  have support := supportCount count alternating live (by decide)
  exact ⟨image, source count alternating, commitments, release (by decide) rom (by decide) support,
    alternatingChanges (2 ^ 30) (show 65536 + count ≤ NativeLayout.sailMemory.upper by decide)⟩

end SP1CleanTest.FixedRamCapacity
