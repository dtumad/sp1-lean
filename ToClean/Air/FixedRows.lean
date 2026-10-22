module

public import Clean.Air.FlatComponent
public import Clean.Circuit.WitnessIRSugar

/-! # Verifier-fixed columns from finite rows

Clean exposes index-addressed fixed-column programs but lacks a constructor for an already
computed rectangular inventory. This adapter uses its existing row IR, including index lookup,
and proves that evaluation recovers each supplied row. Padding and membership policy belong to
the caller. Remove this addition when upstream supplies the corresponding constructor.
-/

@[expose] public section

namespace Air.Flat.FixedColumns

variable {F : Type} {height width : ℕ}

/-- Enumerate exactly the supplied physical rows through Clean's built-in fixed-column IR. -/
def ofRows (rows : Vector (Vector F width) height) (bounded : height < UInt64.size) :
    FixedColumns F where
  height := UInt64.ofNatLT height bounded
  program := .ofFExprs (Vector.ofFn fun column : Fin width =>
    .listGet ((rows.map (·[column.val])).toList.map .const) .idx)
  valid := by
    simp only [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
      Witgen.VExpr.validForRow, Vector.toList_ofFn, List.all_nil, Bool.true_and,
      decide_eq_true_eq, List.all_eq_true, List.forall_mem_ofFn_iff]
    intro column
    simp only [Witgen.FExpr.validForRow, Witgen.U64Expr.validForRow, Bool.and_true]
    exact Witgen.FExprList.validForRow_map_const _ _

/-- All supplied cells are verifier-fixed columns. -/
@[simp] theorem ofRows_width (rows : Vector (Vector F width) height)
    (bounded : height < UInt64.size) : (ofRows rows bounded).width = width := rfl

/-- No physical row is added or dropped by this constructor. -/
@[simp] theorem ofRows_height (rows : Vector (Vector F width) height)
    (bounded : height < UInt64.size) : (ofRows rows bounded).height.toNat = height := rfl

/-- The fixed program recovers the literal inventory, independently of prover data. -/
theorem ofRows_row [FiniteField F] (rows : Vector (Vector F width) height)
    (bounded : height < UInt64.size) (index : Fin height) :
    (ofRows rows bounded).row (UInt64.ofNat index.val) = rows[index].toArray := by
  apply Array.ext
  · simp [row, ofRows, Witgen.RowProgram.ofFExprs]
  · intro column left right
    simp [row, ofRows, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs,
      Witgen.VExpr.eval, Witgen.FExpr.eval, Witgen.U64Expr.eval,
      Witgen.evalList_map_vector_const, Nat.mod_eq_of_lt (index.isLt.trans bounded), index.isLt]

end Air.Flat.FixedColumns
