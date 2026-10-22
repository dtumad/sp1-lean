module

public import Clean.Circuit.Basic
public import Clean.Circuit.Explicit

/-! # Vector witness programs with a literal cell count

`witnessVectorIR` accepts a full program, including shared `letU` steps, and emits a literal
`m`-cell witness operation. Using `witnessIR (fields m)` leaves `size (fields m)` in downstream
offset arithmetic, which structural simp proofs must unfold.

This additive API belongs beside `Circuit.witnessVector` in Clean. It introduces no new witness
semantics: the ordinary vector primitive is the case with no local statements. Remove this
extension and repoint imports when upstream supplies the corresponding API.
-/

@[expose] public section

namespace Circuit

variable {F : Type} [FiniteField F]

/-- Witness a vector of `m` field elements from a witness-IR program, keeping the cell count literal
in the emitted operation (see the module docstring). -/
@[circuit_norm]
def witnessVectorIR (m : ℕ) (ir : Witgen.WitgenIR F m) : Circuit F (Vector (Expression F) m) :=
  fun offset => (varFromOffset (fields m) offset, [.witness m ir])

/-- Explicit operations/length/output, so `elaborate_circuit` and the structural simp sets see this
combinator exactly as they saw the retired native-closure combinator — with the cell count literal.
Mirrors Clean's own instance for `witnessVector`. -/
instance {k : ℕ} : ExplicitCircuits (F := F) (witnessVectorIR k) where
  output _ n := varFromOffset (fields k) n
  localLength _ _ := k
  operations ir n := [.witness k ir]
  channelsWithGuarantees _ _ := []

attribute [explicit_circuit_no_unfold] witnessVectorIR

end Circuit

-- Mirrors Clean's own `export Circuit (witnessVar witnessField witnessVector …)`, so call sites
-- write `witnessVectorIR` unqualified exactly as they write `witnessVector`.
export Circuit (witnessVectorIR)
