module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native U16MSBOperation columns

These circuit value types are owned by the native library. Their field names mirror SP1's
Rust column structs.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `U16MSBOperation`. -/
structure U16MSBOperation (F : Type) where
  /-- Most significant bit of the input 16-bit limb. -/
  msb : F
deriving ProvableStruct
provable_struct_eval_lemmas U16MSBOperation

end SP1Clean.Circuits.Types
