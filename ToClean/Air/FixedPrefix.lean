module

public import Clean.Air.FlatComponent

/-! # Decoding typed fixed cells

Clean exposes fixed-cell agreement but lacks a reusable decoding lemma for a typed fixed payload
followed by private or multiplicity cells. This addition recovers the verifier-fixed prefix
independently of the remaining input.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {Row : TypeMap} [ProvableType Row]

variable {Suffix : TypeMap} [ProvableType Suffix]

/-- Place a typed public prefix before any row-local private and multiplicity cells. -/
def fixedPrefix (row : Witgen.M F (Row (Witgen.FExpr F))) (suffix : Suffix (Cell F)) :
    Witgen.M F (ProvablePair Row Suffix (Cell F)) := do
  let value ← row
  return (fromElements ((toElements value).map .fixed), suffix)

/-- Fixed-cell agreement recovers the full prefix even when private cells share its row. -/
theorem PreallocatedMode.FixedAt.typed_prefix
    {mode : PreallocatedMode F (ProvablePair Row Suffix)}
    {row : Witgen.M F (Row (Witgen.FExpr F))} {i : UInt64}
    {suffix : Suffix (Cell F)} {input : ProvablePair Row Suffix F}
    (program : mode.input .idx = fixedPrefix row suffix)
    (fixed : mode.FixedAt i input) : input.1 = row.evalRow i := by
  simp only [PreallocatedMode.FixedAt, program, fixedPrefix,
    Witgen.M.bind_def, Witgen.M.pure_def, toElements, Vector.toList_append, Vector.toList_map,
    ProvableType.toElements_fromElements, List.forall₂_iff_get] at fixed
  have h : toElements input.1 = toElements (row.evalRow i) := by
    ext j hj
    simpa [List.getElem_append_left, hj, Witgen.M.evalRow, Witgen.eval,
      Cell.FixedMatches, ProvableType.toElements_fromElements, circuit_norm]
      using fixed.2 j (by simp; omega) (by simp; omega)
  simpa [ProvableType.fromElements_toElements] using congrArg (fromElements (M := Row)) h

/-- A typed fixed payload paired with the generator-owned multiplicity cell. -/
def fixedWithMultiplicity (row : Witgen.M F (Row (Witgen.FExpr F))) :
    Witgen.M F (ProvablePair Row field (Cell F)) := fixedPrefix row (.multiplicity : Cell F)

/-- Recover the public payload of a counted fixed provider. -/
theorem PreallocatedMode.FixedAt.input_prefix
    {mode : PreallocatedMode F (ProvablePair Row field)}
    {row : Witgen.M F (Row (Witgen.FExpr F))} {i : UInt64} {input : ProvablePair Row field F}
    (program : mode.input .idx = fixedWithMultiplicity row) (fixed : mode.FixedAt i input) :
    input.1 = row.evalRow i := fixed.typed_prefix program

end Air.Flat.WitnessGeneration
