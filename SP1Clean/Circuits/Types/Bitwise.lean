module

public import SP1Clean.Circuits.Types.U16toU8Operation

/-! # Native bitwise gadget columns

Byte-result columns and operand decompositions share one layout across native contracts,
circuit definitions and proofs.
-/

@[expose] public section

namespace SP1Clean.BitwiseOperation

/-- Local columns for the bytewise bitwise gadget: eight witnessed result bytes. -/
structure Columns (F : Type) where
  /-- Eight little-endian result bytes. -/
  result : Vector F 8
deriving ProvableStruct
provable_struct_eval_lemmas Columns

end SP1Clean.BitwiseOperation

namespace SP1Clean.BitwiseU16Operation

/-- Local columns for the u16 bitwise gadget: two low-byte decomposition blocks and the
native bytewise result block. -/
structure Columns (F : Type) where
  /-- Low bytes of the first operand's four limbs. -/
  b_low_bytes : Circuits.Types.U16toU8Operation F
  /-- Low bytes of the second operand's four limbs. -/
  c_low_bytes : Circuits.Types.U16toU8Operation F
  /-- Eight result bytes supplied to the bytewise assertion. -/
  bitwise_operation : BitwiseOperation.Columns F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

end SP1Clean.BitwiseU16Operation
