import SP1Clean.Proofs.Completeness.ByteDemandMembership
import SP1Clean.Math.SP1Field

/-! # Arithmetic requests outside the released Byte and Range inventories

Each example satisfies the arithmetic test used before physical provider membership was
checked. The independent native dispatcher rejects its complete four-field key.
-/

namespace SP1CleanTest.ByteMembership
open SP1Clean SP1Clean.Soundness
private abbrev F := ZMod SP1Prime

private theorem u8_result :
    let r : ByteRow F := ⟨3,1,7,9⟩
    (r.a.val < 256 ∧ r.b.val < 256 ∧ r.c.val < 256) ∧ ¬ ByteServable (byteLookupKey r) := by
  intro r
  constructor
  · decide
  · rw [← byteRowSpec_iff_servable]
    change ¬ ByteOpcode.constrainField 3 1 7 9
    rw [ByteOpcode.constrainField_three]
    unfold ByteOpcode.constrain
    decide

private theorem msb_unused :
    let r : ByteRow F := ⟨5,1,128,1⟩
    ((r.a = 0 ∨ r.a = 1) ∧ (r.a = 1 ↔ 128 ≤ r.b.val) ∧ r.a.val < 256 ∧ r.b.val < 256 ∧ r.c.val < 256) ∧
      ¬ ByteServable (byteLookupKey r) := by
  intro r
  constructor
  · decide
  · rw [← byteRowSpec_iff_servable]
    change ¬ ByteOpcode.constrainField 5 1 128 1
    rw [ByteOpcode.constrainField_five]
    unfold ByteOpcode.constrain
    decide

private theorem range_unused :
    let r : ByteRow F := ⟨6,1,1,1⟩
    r.a.val < 2^r.b.val ∧ ¬ ByteServable (byteLookupKey r) := by
  intro r
  constructor
  · decide
  · rw [← byteRowSpec_iff_servable]
    change ¬ ByteOpcode.constrainField 6 1 1 1
    rw [ByteOpcode.constrainField_six]
    unfold ByteOpcode.constrain
    decide

private theorem range_width :
    let r : ByteRow F := ⟨6,65536,17,0⟩
    r.a.val < 2^r.b.val ∧ ¬ ByteServable (byteLookupKey r) := by
  intro r
  constructor
  · decide
  · rw [← byteRowSpec_iff_servable]
    change ¬ ByteOpcode.constrainField 6 65536 17 0
    rw [ByteOpcode.constrainField_six]
    unfold ByteOpcode.constrain
    decide

end SP1CleanTest.ByteMembership
