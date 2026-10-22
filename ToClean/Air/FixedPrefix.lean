module

public import Clean.Air.FlatComponent

/-! # Decoding a verifier-fixed input prefix

Clean's typed fixed-input contract exposes a prefix of the flattened input. A paired circuit
needs the corresponding first typed value. This lemma transports that equality without any
condition on the prover-owned suffix or data. Remove it when Clean supplies this decoding rule.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Prefix Suffix : TypeMap} [ProvableType Prefix] [ProvableType Suffix]

/-- The first typed input of a pair is exactly its verifier-fixed prefix. -/
theorem FixedInputAt.input_prefix {fixed : FixedColumns F} {i : UInt64}
    {input : ProvablePair Prefix Suffix F} (width : fixed.width = size Prefix)
    (fixedInput : FixedInputAt (some fixed) i input) :
    (toElements input.1).toArray = fixed.row i := by
  have fixedCells := (fixedInput fixed (by simp)).2
  change (toElements input.1 ++ toElements input.2).toList.take fixed.width =
    (fixed.row i).toList at fixedCells
  rw [Vector.toList_append] at fixedCells
  have same : (toElements input.1).toList = (fixed.row i).toList := by
    simpa [width] using fixedCells
  exact congrArg List.toArray same

end Air.Flat
