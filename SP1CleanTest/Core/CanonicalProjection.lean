import ToClean.Air.EnsembleProjection
import ToClean.Air.MessageFilter
import ToClean.Air.ExpressionScope

/-! # Canonical data under physical prefix projection

A wider source row becomes a narrower target row, one complete table remains, and another table
is removed. The retained key is preserved, while the removed key disappears from derived data.
These cases prevent proof views from relying on the old freely supplied data environment.
Row selection also retains duplicate occurrences and cannot discard required fixed rows.
-/

namespace SP1CleanTest.CanonicalProjection

open Circuit Air.Flat

private abbrev Fp := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- These fixtures inspect projection only; their demand trigger is disabled. -/
private def generation (width : ℕ) : WitnessGeneration.Generation Fp (fields width) :=
  .demand {
    channel := ({ name := "projection.fixture", Guarantees _ _ := True } : Channel Fp field)
    trigger := .pull
    guard _ := .false
    input _ := pure (Vector.replicate width 0) }

private def component (name : String) (width : ℕ) : Component Fp where
  circuit := { GeneralFormalCircuit.empty Fp (fields width) with name := name }
  generation := generation width

private def table (name : String) (row : Array Fp) : Table Fp where
  component := component name row.size
  table := [row]
  data := { tables := fun _ arity => #[rowPrefix arity row], publicInput := #[] }
  length_le := by simp only [List.length_singleton]; decide
  uniform_width := by
    intro candidate member
    obtain rfl := List.mem_singleton.mp member
    rfl
  fixed_rows_match := by trivial
  data_consistent := rfl

private def source : Ensemble Fp unit where
  tables := [component "wide" 3, component "retained" 1, component "removed" 1]
  unique_names := by decide
  channels := []
  unique_channel_names := by simp
  tables_channels := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact List.Subset.refl _
  verifier_channels := by simp [circuit_norm]

private def target : Ensemble Fp unit where
  tables := [component "narrow" 1, component "retained" 1]
  unique_names := by decide
  channels := []
  unique_channel_names := by simp
  tables_channels := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact List.Subset.refl _
  verifier_channels := by simp [circuit_norm]

private def original : EnsembleWitness source :=
  EnsembleWitness.ofTables source
    [table "wide" #[1, 2, 3], table "retained" #[4], table "removed" #[5]] () rfl

private def projected : EnsembleWitness target :=
  original.projectPrefix target (by decide)
    (by intro index; fin_cases index <;> decide)
    (by intro index; fin_cases index <;> rfl)

/-- The narrow view has exactly its declared width and retains the original prefix values. -/
theorem narrowRow : projected.tables[0].table = [#[1]] := by decide

/-- A read at the discarded boundary changes value, so scope checking is necessary for projection. -/
theorem discardedCellIsRejected :
    Backends.expressionBadVariable 1 (Expression.var (F := Fp) ⟨1⟩) = some 1 ∧
      Expression.eval (Environment.fromArray #[1, 2, 3] original.data) (.var ⟨1⟩) ≠
        Expression.eval (Environment.fromArray #[1] projected.data) (.var ⟨1⟩) := by
  decide

/-- An unchanged physical table preserves its named data entry at every arity. -/
theorem retainedData (arity : ℕ) : projected.data.tables "retained" arity = original.data.tables "retained" arity :=
  original.projectPrefix_data_of_same (target := target) (by decide) _ _ ⟨1, by decide⟩ rfl arity

/-- Removing a nonempty table changes canonical data; global data equality would be false. -/
theorem removedData : projected.data.tables "removed" 1 = #[] ∧ original.data.tables "removed" 1 ≠ #[] := by
  decide

private def checkedComponent : Component Fp where
  Input := fields 1
  Output := unit
  generation := generation 1
  circuit := {
    name := "retained"
    main (input : Var (fields 1) Fp) := do
      assertZero input[0]
      return ()
    Spec input _ _ := input[0] = 0
    ProverAssumptions input _ _ := input[0] = 0
    soundness := by circuit_proof_start; simpa only [← h_input, circuit_norm] using h_holds
    completeness := by circuit_proof_start; simpa only [← h_input, circuit_norm] using h_assumptions }

private def checkedTarget : Ensemble Fp unit where
  tables := [component "wide" 3, checkedComponent]
  unique_names := by decide
  channels := []
  unique_channel_names := by simp
  tables_channels := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact List.Subset.refl _
  verifier_channels := by simp [circuit_norm]

private def checkedProjection : EnsembleWitness checkedTarget :=
  original.projectPrefix checkedTarget (by decide)
    (by intro index; fin_cases index <;> exact le_rfl)
    (by intro index; fin_cases index <;> rfl)

/-- Changing the row circuit preserves retained and absent data keys when the input layout is
unchanged. This covers a component replacement, beyond the complete-table identity case. -/
theorem changedCircuitData (name : String) (different : name ≠ "removed") (arity : ℕ) :
    checkedProjection.data.tables name arity = original.data.tables name arity := by
  apply original.projectPrefix_data_of_layout (target := checkedTarget) (by decide) _ _
  · intro index; fin_cases index <;> rfl
  · intro index; fin_cases index <;> rfl
  · intro candidate member
    change candidate ∈ [component "removed" 1] at member
    obtain rfl := List.mem_singleton.mp member
    exact different.symm

/-- Data agreement alone does not preserve constraints: the new zero check rejects the retained
nonzero row. Constraint transport must remain a separate proof obligation. -/
theorem changedCircuitRejectsRow : ¬ checkedProjection.Constraints := by
  intro constraints
  have checked := constraints checkedProjection.tables[1] (List.getElem_mem _) #[4] (by decide)
  change checkedComponent.operations.ConstraintsHold
    (Environment.fromArray #[4] checkedProjection.data) at checked
  simp [Operations.ConstraintsHold, Component.constraints_eq, Component.lookups_eq,
    Component.rowOperations, checkedComponent, circuit_norm] at checked
  exact (by decide : (4 : Fp) ≠ 0) checked

private def repeated : Table Fp where
  component := component "repeated" 1
  table := [#[1], #[0], #[1]]
  data := { tables := fun _ arity => ([#[1], #[0], #[1]].map (rowPrefix arity)).toArray, publicInput := #[] }
  length_le := by decide
  uniform_width := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  fixed_rows_match := by trivial
  data_consistent := rfl

/-- Filtering retains repeated physical occurrences rather than deduplicating their values. -/
theorem repeatedRows :
    (repeated.selectedRows (fun env => decide (env.get 0 = 1))).map (fun env => env.get 0) =
      [1, 1] := by decide

/-- A nonempty fixed table cannot be discarded through the row-selection interface. -/
theorem fixedRowsCannotDisappear (physical : Table Fp)
    (mode : WitnessGeneration.PreallocatedMode Fp physical.component.Input)
    (fixed : physical.component.generation = .preallocated mode) (positive : 0 < mode.height.toNat) :
    ¬ physical.component.FixedRowsMatch (physical.table.filter fun _ => false) := by
  simp only [List.filter_false, Component.FixedRowsMatch, fixed, List.length_nil]
  intro matched
  omega

end SP1CleanTest.CanonicalProjection
