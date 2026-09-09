import SP1Clean.Math.Word

/-! # Little-endian bytes and field words

The memory bus uses four 16-bit limbs while Sail memory stores eight-bit bytes. These lemmas
identify their two encodings without depending on a memory model or an instruction chip.
-/

namespace SP1Clean.Word

/-- Pack eight field-valued bytes into four little-endian limbs. -/
def ofBytes {R : Type} [OfNat R 256] [Add R] [Mul R] (bytes : Vector R 8) : Word R :=
  #v[bytes[0] + (256 : R) * bytes[1], bytes[2] + (256 : R) * bytes[3],
    bytes[4] + (256 : R) * bytes[5], bytes[6] + (256 : R) * bytes[7]]

/-- Sail's little-endian 64-bit interpretation of eight bytes. -/
def bytesValue (bytes : Vector (BitVec 8) 8) : BitVec 64 :=
  bytes[7] ++ bytes[6] ++ bytes[5] ++ bytes[4] ++ bytes[3] ++ bytes[2] ++ bytes[1] ++ bytes[0]

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem pair_val (low high : BitVec 8) :
    ((low.toNat : ZMod p) + 256 * (high.toNat : ZMod p)).val = low.toNat + 256 * high.toNat := by
  have bound : low.toNat + 256 * high.toNat < p := by
    have := low.isLt; have := high.isLt; have := Fact.out (p := 2 ^ 17 < p); omega
  rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from rfl,
    ← Nat.cast_mul, ← Nat.cast_add, ZMod.val_natCast_of_lt bound]

private theorem pair_lt (low high : BitVec 8) :
    ((low.toNat : ZMod p) + 256 * (high.toNat : ZMod p)).val < 2 ^ 16 := by
  rw [pair_val]
  have := low.isLt; have := high.isLt; omega

/-- Genuine bytes always produce a genuine four-limb word. -/
theorem ofBytes_isU64 (bytes : Vector (BitVec 8) 8) :
    isU64 (ofBytes (bytes.map fun byte => (byte.toNat : ZMod p))) := by
  apply isU64_of_cases <;>
    simp only [ofBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Vector.getElem_map]
  all_goals exact pair_lt _ _

private theorem append_byte_toNat {n : ℕ} (high : BitVec n) (low : BitVec 8) :
    (high ++ low).toNat = high.toNat * 256 + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

/-- Field-limb packing and Sail byte concatenation denote exactly the same 64-bit word. -/
theorem toBitVec64_ofBytes (bytes : Vector (BitVec 8) 8) :
    toBitVec64 (ofBytes (bytes.map fun byte => (byte.toNat : ZMod p))) = bytesValue bytes := by
  apply BitVec.eq_of_toNat_eq
  rw [toBitVec64_toNat (ofBytes_isU64 bytes)]
  simp only [toNat, ofBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Vector.getElem_map, pair_val, bytesValue, append_byte_toNat]
  omega

end SP1Clean.Word
