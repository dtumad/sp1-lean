module

public import ToClean.Air.TableBuild

/-! # Evaluating committed rows at explicit data

Clean's table constructor requires its recorded data to agree with its input prefixes. A proof
comparing two inventories may nevertheless evaluate their constraints at a common environment.
These additions express that proof obligation without constructing an inconsistent table.
Generation may use separate data; the resulting table must carry its own consistency proof.
Literal interaction values depend only on cells, while lookup constraints may depend on data.
-/

@[expose] public section

namespace Air.Flat.Table

variable {F : Type} [FiniteField F]

/-- Build rows at explicit generation data and record a consistent evaluation environment. -/
def buildAt (c : Component F) (inputs : List (c.Input F))
    (generationData data : ProverData F) (hint : ProverHint F)
    (bounded : inputs.length ≤ UInt64.size)
    (fixed : c.FixedRowsMatch (inputs.map (c.buildRow · generationData hint)))
    (consistent : data.tables c.circuit.name (size c.Input) = (inputs.map toElements).toArray) :
    Table F where
  component := c
  table := inputs.map (c.buildRow · generationData hint)
  data
  length_le := by simpa only [List.length_map] using bounded
  uniform_width := by
    intro row member
    obtain ⟨input, _, rfl⟩ := List.mem_map.mp member
    exact c.size_buildRow input generationData hint
  fixed_rows_match := fixed
  data_consistent := by
    rw [consistent, List.map_map]
    congr 1
    exact List.map_congr_left fun input _ =>
      (c.rowPrefix_buildRow input generationData hint).symm

/-- The actual constraint system evaluated at another data environment. This does not claim
that the table is consistent with that environment or that its lookup predicates transport. -/
def ConstraintsAt (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ConstraintsHold (Environment.fromArray row data)

/-- All literal interactions can be evaluated at arbitrary data without changing their values. -/
theorem interactions_at (table : Table F) (data : ProverData F) :
    table.interactions = table.table.flatMap (fun row =>
      table.component.operations.interactionValues (Environment.fromArray row data)) := by
  apply congrArg List.flatten
  exact List.map_congr_left fun _ _ => Operations.interactionValues_congr rfl

/-- A selected channel's literal ledger also depends only on the committed cells. -/
theorem interactionsWith_at (table : Table F) (data : ProverData F) (channel : RawChannel F) :
    table.interactionsWith channel = table.table.flatMap (fun row =>
      table.component.operations.interactionValuesWith channel (Environment.fromArray row data)) := by
  apply congrArg List.flatten
  exact List.map_congr_left fun _ _ => Operations.interactionValuesWith_congr rfl

/-- Identical cells and channel expressions determine the same physical ledger, even when
the surrounding ensembles derive different prover data. -/
theorem interactionsWith_eq_of_rows (left right : Table F) (channel : RawChannel F)
    (rows : left.table = right.table)
    (interactions : left.component.operations.interactionsWith channel =
      right.component.operations.interactionsWith channel) :
    left.interactionsWith channel = right.interactionsWith channel := by
  rw [interactionsWith_at left right.data channel, interactionsWith_at right right.data channel, rows]
  simp only [Operations.interactionValuesWith, interactions]

/-- Evaluate generated cells at any data when comparing literal ledgers. -/
theorem buildAt_interactionValues (c : Component F) (inputs : List (c.Input F))
    (generationData data evaluationData : ProverData F) (hint : ProverHint F)
    (bounded fixed consistent) :
    (buildAt c inputs generationData data hint bounded fixed consistent).interactions =
      inputs.flatMap (fun input => c.operations.interactionValues
        (Environment.fromArray (c.buildRow input generationData hint) evaluationData)) := by
  rw [interactions_at _ evaluationData]
  exact List.flatMap_map ..

end Air.Flat.Table
