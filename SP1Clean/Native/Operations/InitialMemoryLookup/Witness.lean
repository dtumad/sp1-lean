import SP1Clean.Model.Core.MemoryTable
import SP1Clean.Circuits.Gadgets.LtUnsigned

/-! # Exportable witnesses for address-based memory reads

The fixed interval selector and unsigned-comparison columns use Clean's field-sorted witness
expressions. Four-limb comparisons retain the exclusive endpoint `2^48` and avoid truncating a
field value to a machine integer. A built-in vector loop emits the interval's nine fields from
one search expression. Evaluation is related to the existing semantic interval search.
-/

namespace SP1Clean.InitialMemoryLookup

open Circuit Witgen Model.Core Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The eight unsigned-comparison cells, using the existing field-sorted limb scan. -/
def comparisonFE (left right : Word (FExpr (ZMod p))) :
    Circuits.Types.LtOperationUnsigned (FExpr (ZMod p)) :=
  ⟨⟨LtOperationUnsigned.compareBitF left right⟩,
    Vector.ofFn (LtOperationUnsigned.flagsF left right),
    LtOperationUnsigned.notEqInvF left right,
    Vector.ofFn (LtOperationUnsigned.comparisonLimbsF left right)⟩

omit [Fact (2 ^ 17 < p)] in
/-- Comparison witnesses evaluate to the native population function. -/
theorem comparisonFE_eval (ctx : Ctx (ZMod p)) (left right : Word (FExpr (ZMod p)))
    (a b : Word (ZMod p))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = a[i])
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = b[i]) :
    Witgen.eval ctx (comparisonFE left right) = LtOperationUnsigned.populate a b := by
  have scan := LtOperationUnsigned.scanF_eval ctx left right a b ha hb
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [comparisonFE, circuit_norm, ProvableStruct.toComponents,
    ProvableStruct.fromComponents, Witgen.eval_fields', Vector.map_ofFn]
  unfold LtOperationUnsigned.populate
  congr 1
  · exact congrArg Circuits.Types.U16CompareOperation.mk scan.2.2.2
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply] using scan.2.1 ⟨i, hi⟩
  · exact scan.2.2.1
  · ext i hi
    simpa only [Vector.getElem_ofFn, Function.comp_apply] using scan.1 ⟨i, hi⟩

/-- Unsigned word comparison as a condition in the existing witness IR. -/
private def lessThanFE (left right : Word (FExpr (ZMod p))) : BExpr (ZMod p) :=
  .flt (LtOperationUnsigned.comparisonLimbsF left right 0)
    (LtOperationUnsigned.comparisonLimbsF left right 1)

private theorem lessThanFE_eval (ctx : Ctx (ZMod p))
    (left right : Word (FExpr (ZMod p))) (a b : Word (ZMod p))
    (ha : ∀ (i : ℕ) (_ : i < 4), left[i].eval ctx = a[i])
    (hb : ∀ (i : ℕ) (_ : i < 4), right[i].eval ctx = b[i])
    (aBound : Word.isU64 a) (bBound : Word.isU64 b) :
    (lessThanFE left right).eval ctx = decide (Word.toNat a < Word.toNat b) := by
  have scan := (LtOperationUnsigned.scanF_eval ctx left right a b ha hb).2.2.2
  have semantic := (LtOperationUnsigned.result_semantic
    (LtOperationUnsigned.spec_populate aBound bBound) rfl).1
  have bit := scan.trans semantic
  change (if (lessThanFE left right).eval ctx then (1 : ZMod p) else 0) =
    (if Word.toNat a < Word.toNat b then 1 else 0) at bit
  cases condition : (lessThanFE left right).eval ctx <;>
    by_cases order : Word.toNat a < Word.toNat b <;> simp_all

/-- Containment compares full four-limb words against the two fixed endpoints. -/
private def containsFE (address : Word (FExpr (ZMod p))) (interval : MemoryInterval) :
    BExpr (ZMod p) :=
  let row := interval.encode (p := p)
  .and (.not (lessThanFE address (row.lower.map FExpr.const)))
    (lessThanFE address (row.upper.map FExpr.const))

private theorem containsFE_eval (ctx : Ctx (ZMod p)) (address : Word (FExpr (ZMod p)))
    (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = value[i])
    (bounded : Word.isU64 value) (interval : MemoryInterval)
    (lower : interval.lower < 2 ^ 64) (upper : interval.upper < 2 ^ 64) :
    (containsFE address interval).eval ctx = decide (interval.Contains (Word.toNat value)) := by
  have low := lessThanFE_eval ctx address ((interval.encode (p := p)).lower.map FExpr.const)
    value (interval.encode (p := p)).lower evaluates
    (by intro i hi; simp only [Vector.getElem_map, FExpr.eval])
    bounded (isU64_bitVecToWord _)
  have high := lessThanFE_eval ctx address ((interval.encode (p := p)).upper.map FExpr.const)
    value (interval.encode (p := p)).upper evaluates
    (by intro i hi; simp only [Vector.getElem_map, FExpr.eval])
    bounded (isU64_bitVecToWord _)
  have endpoints := interval.encode_endpoints (p := p) lower upper
  change (!(lessThanFE address _).eval ctx && (lessThanFE address _).eval ctx) = _
  rw [low, high, endpoints.1, endpoints.2]
  by_cases lowBound : interval.lower ≤ Word.toNat value <;>
    by_cases highBound : Word.toNat value < interval.upper <;>
      simp_all [MemoryInterval.Contains]
  exact decide_eq_false_iff_not.mpr (by omega)

/-- Select one fixed-row field, defaulting to zero outside every interval. -/
def selectFE (address : Word (FExpr (ZMod p)))
    (field : MemoryInterval → ZMod p) : List MemoryInterval → FExpr (ZMod p)
  | [] => 0
  | interval :: rest => .ite (containsFE address interval) (.const (field interval))
      (selectFE address field rest)

/-- The shared interval selector agrees with finite semantic search for every selected field. -/
theorem selectFE_eval (ctx : Ctx (ZMod p)) (address : Word (FExpr (ZMod p)))
    (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval ctx = value[i])
    (bounded : Word.isU64 value) (field : MemoryInterval → ZMod p)
    (rows : List MemoryInterval)
    (bounds : ∀ interval ∈ rows, interval.lower < 2 ^ 64 ∧ interval.upper < 2 ^ 64) :
    (selectFE address field rows).eval ctx =
      ((rows.find? fun interval => decide (interval.Contains (Word.toNat value))).map field).getD 0 := by
  induction rows with
  | nil => rfl
  | cons interval rest ih =>
      have endpoints := bounds interval (List.mem_cons_self ..)
      have condition := containsFE_eval ctx address value evaluates bounded interval
        endpoints.1 endpoints.2
      have tail := ih (fun row member => bounds row (List.mem_cons_of_mem _ member))
      by_cases inside : interval.Contains (Word.toNat value)
      · simp [selectFE, FExpr.eval, condition, inside]
      · simp [selectFE, FExpr.eval, condition, inside, tail]

/-- Select an encoded interval column using the surrounding vector loop's index. -/
private def selectColumnFE (address : Word (FExpr (ZMod p))) :
    List MemoryInterval → FExpr (ZMod p)
  | [] => 0
  | interval :: rest => .ite (containsFE address interval)
      (.listGet ((toElements (interval.encode (p := p))).toList.map FExpr.const) .idx)
      (selectColumnFE address rest)

omit [Fact (2 ^ 17 < p)] in
private theorem evalList_const (ctx : Ctx (ZMod p)) (values : List (ZMod p))
    (index : ℕ) (bound : index < values.length) :
    FExpr.evalList ctx index (values.map FExpr.const) = values[index] := by
  induction values generalizing index with
  | nil => simp at bound
  | cons value rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          exact ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bound)

omit [Fact (2 ^ 17 < p)] in
private theorem selectColumnFE_eval (ctx : Ctx (ZMod p)) (address : Word (FExpr (ZMod p)))
    (rows : List MemoryInterval) (bound : ctx.idx < size MemoryIntervalRow) :
    (selectColumnFE address rows).eval ctx =
      (selectFE address (fun interval => (toElements (interval.encode (p := p)))[ctx.idx]) rows).eval ctx := by
  have small : ctx.idx < 2 ^ 64 := by change ctx.idx < 9 at bound; omega
  induction rows with
  | nil => rfl
  | cons interval rest ih =>
      simp only [selectColumnFE, selectFE, FExpr.eval, U64Expr.eval,
        UInt64.toNat_ofNat', Nat.mod_eq_of_lt small, ih]
      split
      · exact (evalList_const ctx (toElements (interval.encode (p := p))).toList ctx.idx
          (by simpa only [Vector.length_toList] using bound)).trans (Vector.getElem_toList _)
      · rfl

/-- One compact loop emits the nine interval cells without duplicating its search tree. -/
def intervalIR (memory : ByteMemory) (limit : ℕ) (address : Var Word (ZMod p)) :
    WitgenIR (ZMod p) (size MemoryIntervalRow) :=
  .ir [] (.mapRange (size MemoryIntervalRow)
    (selectColumnFE (address.map FExpr.expr) (memory.intervals limit)))

omit [Fact (2 ^ 17 < p)] in
/-- Each loop cell performs the original first-match search, even for malformed addresses. -/
theorem intervalIR_eval_cell (env : ProverEnvironment (ZMod p)) (memory : ByteMemory)
    (limit : ℕ) (address : Var Word (ZMod p)) (index : Fin (size MemoryIntervalRow)) :
    (intervalIR memory limit address |>.eval env)[index.val] =
      (selectFE (address.map FExpr.expr)
        (fun interval => (toElements (interval.encode (p := p)))[index.val])
        (memory.intervals limit)).eval { env, idx := index.val } := by
  simp only [intervalIR, WitgenIR.eval, Witgen.evalSteps, VExpr.getElem_eval_mapRange]
  exact selectColumnFE_eval _ _ _ index.isLt

/-- The compact witness program selects exactly the semantic interval row. -/
theorem intervalIR_eval (env : ProverEnvironment (ZMod p)) (memory : ByteMemory) (limit : ℕ)
    (limitBound : limit < 2 ^ 64) (address : Var Word (ZMod p)) (value : Word (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 4), address[i].eval env.toEnvironment = value[i])
    (bounded : Word.isU64 value) (interval : MemoryInterval)
    (found : memory.intervalAt? limit (Word.toNat value) = some interval) :
    (intervalIR memory limit address).eval env = toElements (interval.encode (p := p)) := by
  have bounds (row : MemoryInterval) (member : row ∈ memory.intervals limit) :
      row.lower < 2 ^ 64 ∧ row.upper < 2 ^ 64 := by
    have endpoints := memory.intervals_bounds limit row member
    exact ⟨lt_of_le_of_lt (endpoints.1.trans endpoints.2) limitBound,
      lt_of_le_of_lt endpoints.2 limitBound⟩
  ext index bound
  rw [intervalIR_eval_cell env memory limit address ⟨index, bound⟩]
  rw [selectFE_eval { env, idx := index } _ value ?_ bounded _ _ bounds]
  · change ((memory.intervalAt? limit (Word.toNat value)).map _).getD 0 = _
    rw [found]
    rfl
  · intro i hi
    simpa only [Vector.getElem_map, FExpr.eval] using evaluates i hi

end SP1Clean.InitialMemoryLookup
