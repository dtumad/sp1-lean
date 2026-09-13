import SP1Clean.Model.Core.Memory

/-! # Executable extensional equality of sparse memory

Comparing update-history lists is too strict, while comparing only a trace's accessed addresses
is too weak. It suffices to compare reads at the union of both histories' keys: every omitted
address has value zero on both sides. The check is finite even for the 48-bit native window.
-/

namespace SP1Clean.Model.Core.ByteMemory

/-- Compare all bytes below a limit using only the finite supports of the two memories. -/
def agreesBelow (left right : ByteMemory) (limit : ℕ) : Bool :=
  (left.entries ++ right.entries).all fun entry =>
    if entry.1 < limit then left.read entry.1 == right.read entry.1 else true

theorem agreesBelow_iff (left right : ByteMemory) (limit : ℕ) :
    left.agreesBelow right limit = true ↔
      ∀ address < limit, left.read address = right.read address := by
  rw [agreesBelow, List.all_eq_true]
  constructor
  · intro checked address bound
    by_cases present : ∃ entry ∈ left.entries ++ right.entries, entry.1 = address
    · obtain ⟨entry, member, equal⟩ := present
      simpa only [equal, if_pos bound, beq_iff_eq] using checked entry member
    · have absent : ∀ entry ∈ left.entries ++ right.entries, entry.1 ≠ address := by
        simpa only [not_exists, not_and] using present
      rw [left.read_eq_zero_of_absent address (fun entry member =>
        absent entry (List.mem_append_left _ member)),
        right.read_eq_zero_of_absent address (fun entry member =>
          absent entry (List.mem_append_right _ member))]
  · intro agrees entry _
    split
    next bound => exact beq_iff_eq.mpr (agrees entry.1 bound)
    next => rfl

end SP1Clean.Model.Core.ByteMemory
