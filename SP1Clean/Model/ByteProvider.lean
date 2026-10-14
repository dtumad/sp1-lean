module

public import SP1Clean.Model.ByteTable

/-! # Exact membership of SP1's byte providers

`ByteRowSpec` is the semantic guarantee used by existing consumers. The actual preprocessed
Byte and Range tables additionally fix unused columns and limit range widths to 16. This
stronger predicate describes their union, independently of a circuit or a lookup count.
-/

@[expose] public section

namespace SP1Clean

/-- A row in the union of SP1's preprocessed Byte and Range tables.
Zero-multiplicity rows must satisfy the same membership predicate as live rows. -/
def ByteProviderSpec {p : ℕ} [NeZero p] (row : ByteRow (ZMod p)) : Prop :=
  ByteRowSpec row ∧
  (row.opcode.val = 3 → row.a = 0) ∧
  (row.opcode.val = 5 → row.c = 0) ∧
  (row.opcode.val = 6 → row.b.val ≤ 16 ∧ row.c = 0)

/-- Exact provider membership supplies the existing byte-channel guarantee. -/
theorem ByteProviderSpec.byteRowSpec {p : ℕ} [NeZero p] {row : ByteRow (ZMod p)}
    (h : ByteProviderSpec row) : ByteRowSpec row := h.1

/-- Exact membership implies a real byte opcode; unknown opcode values are not padding. -/
theorem ByteProviderSpec.opcode_lt {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {row : ByteRow (ZMod p)} (h : ByteProviderSpec row) : row.opcode.val < 7 := by
  obtain ⟨op, hop, _⟩ := h.byteRowSpec
  have hp : 2 ^ 17 < p := Fact.out
  have hi : op.idx < p := by cases op <;> simp only [ByteOpcode.idx] <;> omega
  rw [← hop, ZMod.val_natCast_of_lt hi]
  cases op <;> decide

/-- Decode the semantic predicate at a known valid opcode. -/
theorem byteProviderSpec_iff {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (row : ByteRow (ZMod p)) (h : row.opcode.val < 7) :
    ByteProviderSpec row ↔
      (ByteOpcode.ofNat row.opcode.val).constrain row.a row.b row.c ∧
      (row.opcode.val = 3 → row.a = 0) ∧
      (row.opcode.val = 5 → row.c = 0) ∧
      (row.opcode.val = 6 → row.b.val ≤ 16 ∧ row.c = 0) := by
  rw [← ByteOpcode.constrainField_natCast (k := row.opcode.val) (by omega)]
  simp only [ZMod.natCast_zmod_val, ByteProviderSpec, ByteRowSpec]

end SP1Clean
