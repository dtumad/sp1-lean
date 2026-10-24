module

public import Clean.Circuit.Basic

/-! # Circuit-derived trace rows

Run Clean's witness interpreter on concrete inputs, then evaluate the output columns. Column
order, witness formulas and wiring come from the circuit. `generateTrace` assembles real rows
and zero padding for native conformance fixtures.

These helpers support real-row satisfiability and event-population tests in `SP1CleanTest`.
Built-in Lean-to-Rust export has separate comparisons against released SP1. This sampled path
does not establish all-input witness agreement or compiler completeness.
-/

@[expose] public section

namespace SP1Clean.TraceGenTests

variable {F : Type} [FiniteField F]

/-- Derive one trace row from a circuit: run `main`'s own witness closures on the given input
column values (env-threaded, via `Circuit.proverEnvironment`), then evaluate `main`'s output struct
under the final environment. The circuit is the row generator; `inputs` is the flattened
(`toElements`-ordered) input column list and **must** have length `size Input` — the input
variables `0 … size Input - 1` read it positionally, and local witnesses are allocated after it. -/
def circuitTraceRow (Input : TypeMap) [ProvableType Input] {Output : TypeMap} [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) (inputs : List F)
    (hint : ProverHint F := ProverHint.empty F) : List F :=
  let circ := main (varFromOffset Input 0)
  let env := circ.proverEnvironment hint inputs
  let out : Output (Expression F) := circ.output inputs.length
  (toElements out).toList.map (Expression.eval env.toEnvironment)

/-- Derive a circuit row and apply an explicit complete-row layout map after evaluation.
Native columns may be ordered or factored differently from Rust. This helper does not establish
the map's correctness; independent released-row comparisons own that test boundary. -/
def circuitTraceRowMapped (Input : TypeMap) [ProvableType Input]
    {Output RustOutput : TypeMap} [ProvableType Output] [ProvableType RustOutput]
    (main : Var Input F → Circuit F (Var Output F))
    (reconfigure : Output F → RustOutput F) (inputs : List F)
    (hint : ProverHint F := ProverHint.empty F) : List F :=
  let circ := main (varFromOffset Input 0)
  let env := circ.proverEnvironment hint inputs
  let out : Output (Expression F) := circ.output inputs.length
  (toElements (reconfigure (ProvableType.eval env.toEnvironment out))).toList

/-- Assemble a whole trace matrix from a per-event row generator: derived rows for the real events,
then `padRow` repeated up to `height`. The default all-zero `padRow` mirrors SP1's plain zero-filled
padding; chips with a non-zero `padded_row_template` (the shift chips set the ungated `v_*` power
columns on padding) pass the zero-input derived row instead. -/
def generateTrace {α : Type} (rowGen : α → List F) (events : List α) (height width : ℕ)
    (padRow : List F := List.replicate width 0) : List (List F) :=
  events.map rowGen ++ List.replicate (height - events.length) padRow

end SP1Clean.TraceGenTests
