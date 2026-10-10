module

public import Clean.Air.FlatComponent
public import Clean.Circuit.WitnessIRSugar
public import Clean.Utils.Tactics

/-! # Fixed-column providers for static membership

Clean has static lookup predicates and verifier-fixed column programs, but no typed bridge
between them. This adapter supplies the original predicate through a channel whose provider
rows have verifier-fixed messages and prover-owned multiplicities. It reuses Clean's row IR
and component assumptions; witness scheduling and Rust lowering remain upstream operations.
Delete this addition when Clean supplies the corresponding static-provider API.
-/

@[expose] public section

namespace StaticTable

open Circuit Air.Flat

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- The channel carries the original static predicate, independently of committed prover data. -/
def channel (table : StaticTable F Row) : Channel F Row where
  name := table.name
  Guarantees row _ := table.Spec row

/-- Enumerate the typed table through Clean's index-aware fixed-column IR. -/
def fixedColumns (table : StaticTable F Row) : FixedColumns F where
  height := table.length
  program := .ofFExprs (Vector.ofFn fun column : Fin (size Row) =>
    .listGetAtIndex ((Vector.ofFn fun index : Fin table.length =>
      (toElements (table.row index))[column.val]).toList.map .const))
  valid := by
    simp [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
      Witgen.VExpr.validForRow, Vector.toList_ofFn, Witgen.FExpr.validForRow]
    intro column
    rw [← List.map_ofFn]
    exact Witgen.FExprList.validForRow_map_const _ _

omit [FiniteField F] in
/-- Fixed columns are exactly the message prefix; multiplicities remain committed columns. -/
@[simp] theorem fixedColumns_width (table : StaticTable F Row) :
    table.fixedColumns.width = size Row := rfl

omit [FiniteField F] in
/-- Duplicate rows are retained, and an empty predicate has zero physical rows. -/
@[simp] theorem fixedColumns_height (table : StaticTable F Row) :
    table.fixedColumns.height = table.length := rfl

/-- The canonical row program realizes every enumerated row without a native witness closure. -/
theorem fixedColumns_row (table : StaticTable F Row) (index : Fin table.length) :
    table.fixedColumns.row index.val = (toElements (table.row index)).toArray := by
  apply Array.ext
  · simp [FixedColumns.row, fixedColumns, Witgen.RowProgram.ofFExprs]
  · intro column left right
    simp [FixedColumns.row, fixedColumns, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs,
      Witgen.VExpr.eval, Witgen.FExpr.eval, Witgen.evalList_map_vector_const, index.isLt]

/-- A membership provider emits the authenticated message at its supplied multiplicity.
The enclosing component discharges membership from its fixed prefix, including unused rows. -/
def provider (table : StaticTable F Row) :
    GeneralFormalCircuit F (ProvablePair Row field) unit where
  name := table.name ++ ".provider"
  main input := table.channel.emit input.2 input.1
  Assumptions input _ := table.Spec input.1
  Spec input _ _ := table.Spec input.1
  channelsWithRequirements := [table.channel.toRaw]
  soundness := by
    circuit_proof_start [channel]
    rw [← h_input] at h_assumptions ⊢
    exact ⟨h_assumptions, fun _ _ => h_assumptions⟩
  completeness := by
    circuit_proof_start [channel]

/-- Membership follows from the verifier-fixed prefix, with no residual provider-validity
assumption on the ensemble or its caller. Counts are the only prover-owned input cells. -/
def component (table : StaticTable F Row) : Component F where
  circuit := table.provider
  fixedColumns := some table.fixedColumns
  Assumptions _ _ := True
  assumptions_imply_circuit := by
    intro index row data fixed _ _
    obtain ⟨bound, fixedPrefix⟩ := fixed
    change index < table.length at bound
    rw [fixedColumns_row table ⟨index, bound⟩] at fixedPrefix
    have rowWidth : size Row ≤ row.size := by
      have width := congrArg Array.size fixedPrefix
      simp only [fixedColumns_width, Array.size_extract, Nat.sub_zero,
        Vector.size_toArray] at width
      omega
    change table.Spec ((valueFromOffset (ProvablePair Row field) 0
      (Environment.fromArray row data)).1)
    apply (table.contains_iff _).mp
    refine ⟨⟨index, bound⟩, ?_⟩
    change fromElements (M := Row) _ = table.row ⟨index, bound⟩
    rw [← ProvableType.fromElements_toElements (table.row ⟨index, bound⟩)]
    congr 1
    apply Vector.ext
    intro column columnBound
    have cells := congrArg (fun array : Array F => array[column]?.getD 0) fixedPrefix
    simpa [valueFromOffset, size, ProvablePair.instance, Array.getElem?_extract, Vector.getElem_extract,
      Vector.getElem_mapRange, columnBound, Nat.lt_of_lt_of_le columnBound rowWidth] using cells
  fixed_width_le_input := by
    change size Row ≤ size Row + 1
    omega

end StaticTable
