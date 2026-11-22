module

public import SP1Clean.Semantics.Memory.MemoryFinalCheck
public import SP1Clean.Semantics.Memory.MemorySupport

/-! # Capacity of the complete endpoint change inventory -/

@[expose] public section

namespace SP1Clean.Semantics.MemorySnapshot
open Soundness.Target
/-- A changed cell contains a live byte at one endpoint. Registers contribute at most 32
additional tagged locations, even when a live RAM byte has a low address. -/
theorem changes_length_le_support (source target : MemorySnapshot) :
    (source.changes target).length ≤
      32 + (source.memory.supportBelow (2 ^ 48)).card + (target.memory.supportBelow (2 ^ 48)).card := by
  let regs := (Finset.univ : Finset (BitVec 5)).image MemLoc.reg
  let addresses := source.memory.supportBelow (2 ^ 48) ∪ target.memory.supportBelow (2 ^ 48)
  let cellOf (a : ℕ) := MemLoc.ram (BitVec.ofNat 61 (a / 8))
  have covers : (source.changes target).toFinset ⊆ regs ∪ addresses.image cellOf := by
    intro loc member
    obtain ⟨bound, different⟩ := (mem_changes_iff source target loc).mp (List.mem_toFinset.mp member)
    cases loc with
    | reg idx => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨idx, Finset.mem_univ _, rfl⟩)
    | ram cell =>
      apply Finset.mem_union_right
      by_contra missing
      apply different
      apply congrArg Word.bytesValue
      apply Vector.ext
      intro i small
      let address := cell.toNat * 8 + i
      have inRange : address < 2 ^ 48 := by
        change cell.toNat * 8 < 2 ^ 48 at bound
        dsimp [address]
        omega
      have encoded : cellOf address = .ram cell := by
        have exactCell : address / 8 = cell.toNat := by dsimp [address]; omega
        simp [cellOf, exactCell]
      have absent : address ∉ addresses := fun present => missing (Finset.mem_image.mpr ⟨_, present, encoded⟩)
      have noSrc : source.memory.read address = 0 := by
        by_contra nonzero
        exact absent (Finset.mem_union_left _ ((ByteMemory.mem_supportBelow ..).mpr ⟨inRange, nonzero⟩))
      have noDst : target.memory.read address = 0 := by
        by_contra nonzero
        exact absent (Finset.mem_union_right _ ((ByteMemory.mem_supportBelow ..).mpr ⟨inRange, nonzero⟩))
      simpa only [ByteMemory.wordBytes, Vector.getElem_ofFn] using noSrc.trans noDst.symm
  have regsBound : regs.card ≤ 32 := by
    exact Finset.card_image_le.trans (by decide)
  have cardinal := Finset.card_le_card covers
  rw [List.toFinset_card_of_nodup (changes_nodup _ _)] at cardinal
  have top := Finset.card_union_le regs (addresses.image cellOf)
  have locations := Finset.card_image_le (s := addresses) (f := cellOf)
  have slots := Finset.card_union_le (source.memory.supportBelow (2 ^ 48)) (target.memory.supportBelow (2 ^ 48))
  change addresses.card ≤ _ at slots
  omega
end SP1Clean.Semantics.MemorySnapshot
