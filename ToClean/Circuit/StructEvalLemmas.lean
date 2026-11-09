module

public import Clean.Circuit.StructEvalSimprocs
public import Clean.Utils.Tactics.ProvableStructDeriving
public meta import Lean

/-! # Named projection and congruence lemmas for a `ProvableStruct`

Missing upstream capability: `provable_struct_eval_lemmas S` gives each field a named
`eval_<field>` equation and an `eval_congr_<field>` consequence of whole-row evaluation
agreement. These explicit rewrite and transport APIs complement Clean's generic evaluation
simprocs. Supported structures have one parameter `(F : Type)`.

The equations are deliberately untagged. Clean's normal form lifts evaluations of projections
to projections of the evaluated row; automatically rewriting them in the reverse direction
would form a loop. Callers use the named equations only where a cell-wise representation is
needed. The generated proofs destructure a row and use definitional equality, without
normalizing all of its fields for each projection.
-/

@[expose] public section

namespace ProvableStruct

variable {F : Type} [FiniteField F]

/-- The cell-wise reading of "the evaluated struct variable at `offset` is `w`" (the shape a
`witnessVector`-style witness condition takes once `circuit_norm` has decomposed
`varFromOffset α offset` into a literal): cell `j` of the environment is cell `j` of `w`'s
flattening. Fold the literal back with `change ProvableStruct.eval env
(ProvableStruct.varFromOffset α offset) = _ at h` (definitional) and apply. -/
theorem get_of_eval_varFromOffset_eq {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (offset : ℕ) (w : α F)
    (h : ProvableStruct.eval env (ProvableStruct.varFromOffset α offset) = w)
    (j : ℕ) (hj : j < size α) : env.get (offset + j) = (toElements w)[j] := by
  subst h
  rw [← ProvableStruct.eval_eq_eval, ← ProvableStruct.varFromOffset_eq_varFromOffset,
    ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]

end ProvableStruct

open Lean Elab Command Meta

namespace ProvableStruct

/-- `provable_struct_eval_lemmas S` declares `S.eval_<field> : (ProvableStruct.eval env s).<field> =
Eval.eval env s.<field>` for every field of `S`, together with field-wise congruence
consequences. The equations are explicit rewrite APIs, not normalization rules. -/
elab "provable_struct_eval_lemmas " id:ident : command => do
  let structName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let some info := getStructureInfo? env structName
    | throwErrorAt id "`{structName}` is not a structure"
  let some (.inductInfo indInfo) := env.find? structName
    | throwErrorAt id "`{structName}` is not an inductive type"
  unless indInfo.numParams == 1 do
    throwErrorAt id "`{structName}` must have exactly one parameter `(F : Type)`"
  let structIdent := mkIdent structName
  for field in info.fieldNames do
    -- `_root_`: the generated name is absolute, whatever namespace the command sits in.
    let lemmaIdent := mkIdent (`_root_ ++ structName ++ Name.mkSimple s!"eval_{field}")
    let fieldIdent := mkIdent field
    let some projFn := getProjFnForField? env structName field
      | throwErrorAt id "no projection function for field `{field}` of `{structName}`"
    -- 0 = scalar (`F`); 1 = `Vector F n` (`Word F`, `fields n F` included); 3 = a vector of
    -- something else (a `ProvableVector`); 2 = a nested struct or anything else.
    let kind : Nat ← liftTermElabM do
      forallTelescopeReducing (← getConstInfo projFn).type fun xs body => do
        if body == xs[0]! then pure 0
        else
          let body' ← whnfD body
          if body'.isAppOfArity ``Vector 2 then
            pure (if body'.getAppArgs[0]! == xs[0]! then 1 else 3)
          else pure 2
    -- Proof: on the constructor literal `cases s` exposes, `ProvableStruct.eval` reduces
    -- definitionally (`toComponents` / `eval.go` / `fromComponents` all compute), so the
    -- projection is `rfl`. A `simp only [circuit_norm]` here normalises the WHOLE struct's
    -- evaluation before projecting — quadratic in the field count (45-field `DivRemChip.Columns`:
    -- 27 s of `simp` for its 45 lemmas, 5 s with `rfl`; measured 2026-09-22).
    let cmd ← `(
      theorem $lemmaIdent:ident {F : Type} [FiniteField F] (env : Environment F)
          (s : Var $structIdent F) :
          (ProvableStruct.eval env s).$fieldIdent:ident = Eval.eval env s.$fieldIdent:ident := by
        cases s
        rfl)
    elabCommand cmd
    -- `S.eval_congr_f : eval env s = eval env' s → <field f of s agrees>`, stated in the field's
    -- `circuit_norm` normal form so `rw`/`exact` at a constraint-form goal need no further step.
    -- Proof: project `h`, rewrite both sides with the field's `eval_f` lemma just proved, then the
    -- one Clean lemma that puts the field's kind into that normal form — never the whole
    -- `circuit_norm` set (which re-normalises the entire struct evaluation per lemma).
    let congrIdent := mkIdent (`_root_ ++ structName ++ Name.mkSimple s!"eval_congr_{field}")
    let congrCmd ← match kind with
      | 0 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Expression.eval env s.$fieldIdent:ident = Expression.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident, ProvableType.eval_field,
            ProvableType.eval_field] at this
          exact this)
      | 1 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Eval.eval env s.$fieldIdent:ident
              = Eval.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident] at this
          exact this)
      | 2 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            ProvableStruct.eval env s.$fieldIdent:ident
              = ProvableStruct.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident, ProvableStruct.eval_eq_eval,
            ProvableStruct.eval_eq_eval] at this
          exact this)
      | _ => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Eval.eval env s.$fieldIdent:ident = Eval.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident] at this
          exact this)
    elabCommand congrCmd

end ProvableStruct
