module

public import Clean.Air.RowProgram
public import Clean.Circuit.WitnessIRSugar

/-! # Typed literal rows in the witness IR

Clean exposes index-addressed row programs but lacks a constructor for an already computed
rectangular inventory. This constructor uses its existing witness IR and proves that evaluation
recovers each supplied typed row. Padding and membership policy belong to the caller.
-/

@[expose] public section

namespace Witgen

variable {F : Type} {Row : TypeMap} [ProvableType Row] {height : ℕ}

/-- Enumerate supplied typed rows through the canonical index-addressed witness IR. -/
def literalRow (rows : Vector (Row F) height) (index : U64Expr F) : M F (Row (FExpr F)) :=
  pure (fromElements (Vector.ofFn fun column : Fin (size Row) =>
    .listGet ((rows.map (fun row => (toElements row)[column.val])).toList.map .const) index))

/-- The literal program recovers each inventory row without reading hints or prover data. -/
theorem literalRow_evalRow [FiniteField F] (rows : Vector (Row F) height)
    (bounded : height < UInt64.size) (index : Fin height) :
    (literalRow rows .idx).evalRow (UInt64.ofNat index.val) = rows[index] := by
  suffices same : toElements ((literalRow rows .idx).evalRow (UInt64.ofNat index.val)) =
      toElements rows[index] by
    simpa only [ProvableType.fromElements_toElements] using
      congrArg (fromElements (M := Row)) same
  ext column
  simp [literalRow, M.pure_def, M.evalRow, Witgen.eval, ProvableType.toElements_fromElements, FExpr.eval, U64Expr.eval,
    evalList_map_vector_const, Nat.mod_eq_of_lt (index.isLt.trans bounded), index.isLt]

end Witgen
