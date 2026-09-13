import SP1Clean.Soundness.RowEffectDefs
import SP1Clean.FormalModel.Contracts.WritePermission

/-! # ROM preservation from the actual byte footprint

The chip bridge already proves that a store frames every byte outside its committed write.
Permission for those written bytes therefore preserves instruction memory, including code sharing
an eight-byte RAM cell with writable data. No property of unrelated interpreter steps is needed.
-/

namespace SP1Clean.Soundness.Target

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Permission refers to the committed write footprint, rather than an entire RAM bus cell. -/
def RowWritePermitted (image : ProgramImage) (row : Trace.RowView (ZMod p)) : Prop :=
  ∀ write, row.commit.memWrite = some write →
    ∀ address, write.covers address → image.readOnly address = false

/-- The byte requests cover the semantic write range, including its final byte. -/
theorem write_readOnly_false_of_permissions (image : ProgramImage)
    (write : Trace.MemWrite (ZMod p)) (widthBound : write.width ≤ 2 ^ 16)
    (permissions : ∀ index : Fin write.width,
      WritePermissionProvider.Permitted image (Address.offset write.addr (index.val : ZMod p)))
    (address : ℕ) (covered : write.covers address) : image.readOnly address = false := by
  change Address.toNat write.addr ≤ address ∧ address < Address.toNat write.addr + write.width at covered
  have positive : 0 < write.width := by omega
  have bounded : Address.Bounded write.addr := by
    simpa only [Nat.cast_zero, Address.offset_zero] using (permissions ⟨0, positive⟩).1
  let index : Fin write.width := ⟨address - Address.toNat write.addr, by omega⟩
  have permitted := (permissions index).2.2
  rw [Address.toNat_offset write.addr bounded index.val (by have := index.isLt; omega)] at permitted
  have same : Address.toNat write.addr + index.val = address := by dsimp only [index]; omega
  rwa [same] at permitted

theorem RowEffect.romLoaded_of_writePermission {image : ProgramImage} (valid : image.Valid)
    {row : Trace.RowView (ZMod p)} {state next : SailState}
    (effect : RowEffect (image.toGuestProgram valid) row state next)
    (permitted : RowWritePermitted image row)
    (loaded : RomLoaded (image.toGuestProgram valid) state) :
    RomLoaded (image.toGuestProgram valid) next := by
  intro pc word fetched index
  have readonly : image.readOnly (pc.toNat + index) = true := by
    obtain ⟨entry, found, wordEq⟩ := Option.map_eq_some_iff.mp fetched
    have member : entry ∈ image.rom := List.mem_of_find?_eq_some found
    have atPc : entry.1 = pc := by simpa using List.find?_some found
    apply (image.readOnly_iff _).mpr
    exact ⟨entry, member, by rw [atPc]; omega, by rw [atPc]; have := index.isLt; omega⟩
  have frame : next.mem.get? (pc.toNat + index) = state.mem.get? (pc.toNat + index) := by
    cases write : row.commit.memWrite with
    | none => exact effect.mem.1 write _
    | some footprint =>
        apply (effect.mem.2 footprint write).2
        intro covered
        have denied := permitted footprint write _ covered
        rw [readonly] at denied
        contradiction
  exact frame.trans (loaded pc word fetched index)

end SP1Clean.Soundness.Target
