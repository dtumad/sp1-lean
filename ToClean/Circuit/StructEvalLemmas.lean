import Clean.Circuit.StructEvalSimprocs
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Per-field evaluation lemmas for a `ProvableStruct`

**Gap against upstream.** Clean's `circuit_norm` normal form for struct evaluation is
component-preserving: `ProvableStruct.eval env ⟨a, b⟩` on a *literal* decomposes into
`⟨eval env a, eval env b⟩` (the `StructEvalSimprocs`), and `Expression.eval env s.x` on a
*variable* `s` is meant to lift to `(ProvableStruct.eval env s).x`. The lift never fires: its
proof needs `toComponents s` to reduce on a variable, which matchers no longer do (the doc-comment
of `StructEvalSimprocs.lean` records the same change). So a proof that holds a row-level fact
`(ProvableStruct.eval env s).x = …` against a goal in the constraint form `Expression.eval env s.x`
has no `circuit_norm` bridge, and Clean's own `Examples/FemtoCairo/TypesLemmas.lean` writes the
bridge by hand, once per field:

```lean
@[circuit_norm] lemma State.eval_pc (env : Environment F) (s : Var State F) :
    (eval env s).pc = Expression.eval env s.pc := by
  obtain ⟨pc, ap, fp⟩ := s
  simp [circuit_norm, explicit_provable_type]
```

`provable_struct_eval_lemmas S` generates exactly those lemmas for every field of `S` (proof:
`cases s; simp only [circuit_norm]`, so the right-hand side lands in whatever normal form the
field's type has — `Expression.eval` for a scalar, `Vector.map (Expression.eval env)` for a
`Vector F n`, `ProvableStruct.eval` for a nested struct). Scalar and nested-struct lemmas are
`circuit_norm` members; a `Vector F n` field's lemma is declared but left untagged, because
Clean's indexing simproc does lift `Expression.eval env s.c[i]` to `(ProvableStruct.eval env s).c[i]`
and the two would loop. Upstream home: the `deriving ProvableStruct` handler, next to the
`fromComponents_cons` lemma it already emits. Supported shape: a structure whose only parameter
is `(F : Type)`. -/

open Lean Elab Command Meta

namespace ProvableStruct

/-- `provable_struct_eval_lemmas S` declares `S.eval_<field> : (ProvableStruct.eval env s).<field> =
Eval.eval env s.<field>` (tagged `circuit_norm`) for every field of the structure `S`. -/
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
    -- A `Vector F n` field keeps Clean's lifted normal form (`(ProvableStruct.eval env s).c[i]`,
    -- which Clean's indexing simproc does produce), so its lemma is not a `circuit_norm` member:
    -- tagging it would loop against that simproc through `eval_fields`/`getElem_map`.
    let some projFn := getProjFnForField? env structName field
      | throwErrorAt id "no projection function for field `{field}` of `{structName}`"
    let isVector ← liftTermElabM do
      forallTelescopeReducing (← getConstInfo projFn).type fun _ body =>
        pure (body.isAppOfArity ``Vector 2)
    let cmd ← if isVector then `(
      theorem $lemmaIdent:ident {F : Type} [FiniteField F] (env : Environment F)
          (s : Var $structIdent F) :
          (ProvableStruct.eval env s).$fieldIdent:ident = Eval.eval env s.$fieldIdent:ident := by
        cases s
        simp only [circuit_norm])
    else `(
      @[circuit_norm]
      theorem $lemmaIdent:ident {F : Type} [FiniteField F] (env : Environment F)
          (s : Var $structIdent F) :
          (ProvableStruct.eval env s).$fieldIdent:ident = Eval.eval env s.$fieldIdent:ident := by
        cases s
        simp only [circuit_norm])
    elabCommand cmd

end ProvableStruct
