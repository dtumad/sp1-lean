module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.LtOperationUnsigned
public import SP1Clean.Circuits.Types.U16MSBOperation

/-! # Native LtOperationSigned columns

These circuit value types are owned by the native library. Their field names mirror SP1's
Rust column structs.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `LtOperationSigned`. -/
structure LtOperationSigned (F : Type) where
  /-- Unsigned comparison of the operand words. -/
  result : (LtOperationUnsigned F)
  /-- Most significant bit of the first operand. -/
  b_msb : (U16MSBOperation F)
  /-- Most significant bit of the second operand. -/
  c_msb : (U16MSBOperation F)
deriving ProvableStruct
provable_struct_eval_lemmas LtOperationSigned

-- Temporary: field names mirror SP1's Rust column structs; rename them to lowerCamelCase
-- together with their consumers (#16).
attribute [nolint defsWithUnderscore]
  LtOperationSigned.b_msb
  LtOperationSigned.c_msb

end SP1Clean.Circuits.Types
