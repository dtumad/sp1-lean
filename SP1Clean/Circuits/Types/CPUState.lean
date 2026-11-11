module

public import Clean.Circuit.Provable
public import ToClean.Circuit.StructEvalLemmas

/-! # Native CPUState columns

These circuit value types are owned by the native library. Their field names mirror SP1's
Rust column structs.
-/

@[expose] public section

namespace SP1Clean.Circuits.Types

/-- Circuit columns for `CPUState`. -/
structure CPUState (F : Type) where
  /-- Clock bits above bit 23. -/
  clk_high : F
  /-- Clock bits 16 through 23. -/
  clk_16_24 : F
  /-- Low 16 clock bits. -/
  clk_0_16 : F
  /-- Program counter in three little-endian 16-bit limbs. -/
  pc : (Vector F 3)
deriving ProvableStruct
provable_struct_eval_lemmas CPUState

-- Temporary: field names mirror SP1's Rust column structs; rename them to lowerCamelCase
-- together with their consumers (#16).
attribute [nolint defsWithUnderscore]
  CPUState.clk_high
  CPUState.clk_16_24
  CPUState.clk_0_16

end SP1Clean.Circuits.Types
