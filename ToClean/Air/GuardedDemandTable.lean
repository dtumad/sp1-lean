module

public import ToClean.Air.DemandPadding
public import ToClean.Air.TableBuild

/-! # Compiling private unit-demand tables at their canonical padded height

Clean provides the demand scheduler and the underlying certified row builder. These helpers
construct its explicit active/padding input sequence, prove the guarded row assumptions,
and build the table using its own consistent private-input columns.
-/

@[expose] public section

namespace Air.Flat.WitnessGeneration
open Circuit

/-- Unit-weight inputs followed by zero-weight, zero-input rows at Clean's demand height. -/
def guardedRows {I F : Type} [Zero I] [Zero F] [One F] (inputs : List I) : List (I × F) :=
  inputs.map (fun input => (input, 1)) ++ List.replicate (demandPadding inputs.length) 0

theorem guardedRows_length {I F : Type} [Zero I] [Zero F] [One F] (inputs : List I) :
    (guardedRows (F := F) inputs).length = demandHeight inputs.length := by
  simp [guardedRows, add_demandPadding]

/-- A guarded circuit inherits its prover obligation on each active input. -/
theorem guardedRows_all {I F : Type} [Zero I] [FiniteField F] (P : I → Prop) {inputs : List I}
    (valid : ∀ i ∈ inputs, P i) :
    ∀ row ∈ guardedRows (F := F) inputs, IsBool row.2 ∧ (row.2 = 1 → P row.1) := by
  intro row member
  rcases List.mem_append.mp member with active | padding
  · obtain ⟨input, present, rfl⟩ := List.mem_map.mp active
    exact ⟨Or.inr rfl, fun _ => valid input present⟩
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp padding
    exact ⟨Or.inl rfl, fun impossible => (zero_ne_one impossible).elim⟩

end Air.Flat.WitnessGeneration

namespace Air.Flat.Table
open Circuit

variable {F : Type} [FiniteField F]

/-- Generate rows at consistent component input data; each demand table carries its
structural fixed-column fact through its concrete generation mode. -/
def ofInputs (c : Component F) (inputs : List (c.Input F)) (data : ProverData F) (bound : inputs.length ≤ UInt64.size)
    (demand : ∀ rs, c.FixedRowsMatch rs) : Table F :=
  build c inputs (c.inputData inputs data) (.empty _) bound (demand _) (c.inputData_consistent inputs data)

theorem ofInputs_valid (c : Component F) (inputs : List (c.Input F)) (data : ProverData F) (bound demand)
    (honest : ∀ i ∈ inputs, c.circuit.ProverAssumptions i (c.inputData inputs data) (.empty _)) :
    (ofInputs c inputs data bound demand).Constraints ∧ (ofInputs c inputs data bound demand).Guarantees := by
  unfold ofInputs
  constructor
  · apply build_constraints
    exact honest
  · apply build_guarantees
    exact honest

theorem ofInputs_length (c : Component F) (inputs : List (c.Input F)) (data : ProverData F) (bound demand) :
    (ofInputs c inputs data bound demand).table.length = inputs.length :=
  List.length_map ..

/-- Evaluate the original typed interactions on the generated physical row inputs. -/
theorem ofInputs_ledger (c : Component F) (inputs : List (c.Input F)) (data : ProverData F) (bound demand)
    (channel : RawChannel F) (values : c.Input F → List (Interaction F))
    (point : ∀ env, c.operations.interactionValuesWith channel env = values (c.rowInput env)) :
    (ofInputs c inputs data bound demand).interactionsWith channel = inputs.flatMap values := by
  unfold ofInputs
  rw [build_interactions]
  apply List.flatMap_congr
  intro row _
  exact (point _).trans (congrArg values (c.rowInput_buildRow row _ _ _))

end Air.Flat.Table
