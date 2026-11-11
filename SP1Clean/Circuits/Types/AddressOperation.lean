module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas
public import SP1Clean.Circuits.Types.AddrAddOperation

/-! # Native AddressOperation columns

These circuit value types are owned by the native library. Their field names mirror SP1's
Rust column structs.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `AddressOperation`. -/
structure AddressOperation (F : Type) where
  /-- Three-limb effective-address addition. -/
  addr_operation : (AddrAddOperation F)
  /-- Inverse witness for the sum of the upper address limbs. -/
  top_two_limb_inv : F
deriving ProvableStruct
provable_struct_eval_lemmas AddressOperation

-- Temporary: field names mirror SP1's Rust column structs; rename them to lowerCamelCase
-- together with their consumers (#16).
attribute [nolint defsWithUnderscore]
  AddressOperation.addr_operation
  AddressOperation.top_two_limb_inv

end SP1Clean.Circuits.Types
