module

public import Clean.Air.FlatComponent

/-! # Decoding typed fixed cells

Clean exposes fixed-cell agreement but lacks a reusable decoding lemma for a typed fixed payload
paired with a multiplicity. This addition recovers the payload without restricting the count.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {Row : TypeMap} [ProvableType Row]

/-- A typed fixed payload paired with the generator-owned multiplicity cell. -/
def fixedWithMultiplicity (row : Witgen.M F (Row (Witgen.FExpr F))) :
    Witgen.M F (ProvablePair Row field (Cell F)) := do
  let value ← row
  return (fromElements ((toElements value).map .fixed), .multiplicity)

/-- Fixed-cell agreement authenticates the entire typed payload independently of its count. -/
theorem PreallocatedMode.FixedAt.input_prefix
    {mode : PreallocatedMode F (ProvablePair Row field)}
    {row : Witgen.M F (Row (Witgen.FExpr F))} {i : UInt64}
    {input : ProvablePair Row field F}
    (program : mode.input .idx = fixedWithMultiplicity row)
    (fixed : mode.FixedAt i input) : input.1 = row.evalRow i := by
  simp only [PreallocatedMode.FixedAt, program, fixedWithMultiplicity,
    Witgen.M.bind_def, Witgen.M.pure_def, toElements, Vector.toList_append, Vector.toList_map,
    ProvableType.toElements_fromElements, List.forall₂_iff_get] at fixed
  have h : toElements input.1 = toElements (row.evalRow i) := by
    ext j hj
    simpa [List.getElem_append_left, hj, Witgen.M.evalRow, Witgen.eval,
      Cell.FixedMatches, ProvableType.toElements_fromElements, circuit_norm]
      using fixed.2 j (by simp; omega) (by simp; omega)
  simpa [ProvableType.fromElements_toElements] using congrArg (fromElements (M := Row)) h

end Air.Flat.WitnessGeneration
