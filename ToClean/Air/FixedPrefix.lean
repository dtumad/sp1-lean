module

public import Clean.Air.FlatComponent

/-! # Decoding a verifier-fixed input prefix

Clean exposes fixed-row equality on physical arrays. Typed provider proofs additionally need
the decoded prefix of a paired circuit input. This lemma transports that equality without
assuming anything about the prover-owned suffix or the semantic data environment.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Prefix Suffix : TypeMap} [ProvableType Prefix] [ProvableType Suffix]

/-- A verifier-fixed physical prefix determines the first typed input of a paired circuit. -/
theorem FixedRowAt.input_prefix {fixed : FixedColumns F} {i : ℕ} {row : Array F}
    (data : ProverData F) (width : fixed.width = size Prefix)
    (fixedRow : FixedRowAt (some fixed) i row) :
    (valueFromOffset (ProvablePair Prefix Suffix) 0 (Environment.fromArray row data)).1 =
      fromElements (inputRow Prefix (fixed.row i)) := by
  change fromElements _ = fromElements _
  congr 1
  apply Vector.ext
  intro column bound
  have rowWidth : size Prefix ≤ row.size := by
    have sizes := congrArg Array.size fixedRow.2
    simp [FixedColumns.row, width] at sizes
    omega
  have cells := congrArg (fun array : Array F => array[column]?.getD 0) fixedRow.2
  simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_mapRange]
  simpa [inputRow, Array.getElem?_extract, width, bound, Nat.lt_of_lt_of_le bound rowWidth] using cells

end Air.Flat
