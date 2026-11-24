module

public import SP1Clean.Semantics.Specs.U16toU8Safe
public import SP1Clean.Math.ByteWord
import Mathlib.Tactic.IntervalCases
import SP1Clean.Math.Bitwise

/-! # Little-endian lanes from the safe SP1 byte decomposition -/

@[expose] public section

namespace SP1Clean.U16toU8OperationSafe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Put four pairs of low/high field bytes into guest little-endian lane order. -/
def bytes {R : Type} [Sub R] [Mul R] (inverse : R) (value low : Word R) : Vector R 8 :=
  #v[low[0], (value[0] - low[0]) * inverse, low[1], (value[1] - low[1]) * inverse,
    low[2], (value[2] - low[2]) * inverse, low[3], (value[3] - low[3]) * inverse]

/-- The eight range-checked lanes encode the complete input word. -/
theorem DecompSpec.bytes {value low : Word (ZMod p)} (decoded : DecompSpec value ⟨low⟩) :
    let lanes := U16toU8OperationSafe.bytes (256 : ZMod p)⁻¹ value low
    (∀ index : Fin 8, lanes[index].val < 256) ∧
      value.toBitVec64 = Word.bytesValue (lanes.map fun byte => BitVec.ofNat 8 byte.val) := by
  let lanes := U16toU8OperationSafe.bytes (256 : ZMod p)⁻¹ value low
  have bounded : ∀ index : Fin 8, lanes[index].val < 256 := by
    intro index
    fin_cases index
    · exact (decoded 0).1
    · exact (decoded 0).2.1
    · exact (decoded 1).1
    · exact (decoded 1).2.1
    · exact (decoded 2).1
    · exact (decoded 2).2.1
    · exact (decoded 3).1
    · exact (decoded 3).2.1
  have packed : Word.ofBytes lanes = value := by
    apply Vector.ext
    intro index bound
    interval_cases index
    all_goals simp only [Word.ofBytes, lanes, U16toU8OperationSafe.bytes, circuit_norm]
    all_goals rw [mul_left_comm, mul_inv_cancel₀ val_256_ne_zero, mul_one, add_sub_cancel]
  exact ⟨bounded, (congrArg Word.toBitVec64 packed).symm.trans (Word.toBitVec64_ofByteFields _ bounded)⟩

end SP1Clean.U16toU8OperationSafe
