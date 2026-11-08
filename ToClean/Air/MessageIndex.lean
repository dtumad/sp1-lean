module

public import Clean.Air.RowProgram

/-! # First matching message index in the existing witness IR

Clean's preallocated routing uses an explicit index into the physical rows. This additive authoring helper selects the first complete payload using
Clean's existing conditionals; the scheduler still validates the selected interaction's full
message. It introduces no evaluator or scheduler. Replace it when upstream supplies a canonical
first-match index constructor. The linear expression is a correctness path, not a scalable index.
-/

@[expose] public section

namespace Witgen

variable {F : Type}

/-- Compare a literal payload with consecutive fields of the triggering message. -/
def BExpr.messageMatches : List F → ℕ → BExpr F
  | [], _ => .true
  | cell :: rest, column =>
      .and (.feq (.expr (.var ⟨column⟩)) (.const cell)) (messageMatches rest (column + 1))

/-- Choose the first matching payload. A miss returns the explicit out-of-range index;
the scheduler's full-message check rejects a missing or mismatching candidate, including padding.
Offsets use the same bounded row-index type as Clean's preallocated tables. -/
def U64Expr.messageIndex {width : ℕ} : List (Vector F width) → UInt64 → UInt64 → U64Expr F
  | [], _, missing => .const missing
  | row :: rest, offset, missing =>
      .ite (BExpr.messageMatches row.toList 0) (.const offset) (messageIndex rest (offset + 1) missing)

end Witgen
