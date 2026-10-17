module

public import Clean.Air.RowProgram

/-! # First matching message index in the existing witness IR

Clean's default preallocated routing requires a unique physical match, so repeated fixed rows
need an explicit index. This additive authoring helper selects the first complete payload using
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

/-- Literal payload comparisons read only message fields. -/
theorem BExpr.messageMatches_valid (cells : List F) (column : ℕ) :
    (messageMatches cells column).validForRow .message = Bool.true := by
  induction cells generalizing column with
  | nil => rfl
  | cons cell rest ih =>
      simp [messageMatches, BExpr.validForRow, FExpr.validForRow, ih]

/-- Choose the first matching payload. A miss returns the index after the supplied inventory;
the scheduler's full-message check rejects a missing or mismatching candidate, including padding.
Offsets use the same bounded row-index type as Clean's preallocated tables. -/
def U64Expr.messageIndex {width : ℕ} : List (Vector F width) → UInt64 → U64Expr F
  | [], offset => .const offset
  | row :: rest, offset =>
      .ite (BExpr.messageMatches row.toList 0) (.const offset) (messageIndex rest (offset + 1))

/-- Routing reads only the triggering message and the literal fixed inventory. -/
theorem U64Expr.messageIndex_valid {width : ℕ} (rows : List (Vector F width)) (offset : UInt64) :
    (messageIndex rows offset).validForRow .message = Bool.true := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rest ih => simp [messageIndex, validForRow, BExpr.messageMatches_valid, ih]

end Witgen
