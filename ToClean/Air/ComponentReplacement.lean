module

public import ToClean.Air.TableSlot
public import ToClean.Air.EnsembleProjection

/-! # Replacing a registered component without changing its physical rows

Clean has no introduction rule for changing a table's circuit while preserving its complete
rows. This addition requires equal widths and fixed-column contracts. Replacing an ensemble
component uses a typed slot and preserves its name, so the physical inventory remains unique.
Canonical data is preserved only after proving equality of the replacement's derived entries.

These layout and data transport lemmas belong beside Clean's flat tables and ensembles. They
do not construct witnesses or supply another extraction path.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- Reinterpret complete rows only when both physical layout obligations are preserved. -/
def Table.withComponent (table : Table F) (component : Component F)
    (width : component.width = table.component.width)
    (fixed : component.FixedRowsMatch = table.component.FixedRowsMatch)
    (name : component.circuit.name = table.component.circuit.name := by rfl)
    (inputWidth : size component.Input = size table.component.Input := by rfl) : Table F where
  component
  table := table.table
  data := table.data
  length_le := table.length_le
  uniform_width := fun row member => (table.uniform_width row member).trans width.symm
  fixed_rows_match := by
    exact fixed.symm ▸ table.fixed_rows_match
  data_consistent := by
    rw [name, inputWidth]
    exact table.data_consistent

/-- Changing only the component keeps the literal physical rows. -/
@[simp] theorem Table.withComponent_rows (table : Table F) (component : Component F) (width fixed name inputWidth) :
    (table.withComponent component width fixed name inputWidth).table = table.table := rfl

@[simp] theorem Table.withComponent_component (table : Table F) (component : Component F) (width fixed name inputWidth) :
    (table.withComponent component width fixed name inputWidth).component = component := rfl

/-- Replacing a table by itself retains its width and fixed-column certificates. -/
@[simp] theorem Table.withComponent_self (table : Table F) :
    table.withComponent table.component rfl rfl rfl rfl = table := by
  cases table
  rfl

namespace Table

variable (table : Table F) (component : Component F) (width fixed name inputWidth)

/-- A proved implication between row circuits lifts to all retained physical rows. -/
theorem withComponent_constraints_of
    (preserves : ∀ env, table.component.operations.ConstraintsHold env →
      component.operations.ConstraintsHold env) (checked : table.Constraints) :
    (table.withComponent component width fixed name inputWidth).Constraints :=
  fun row member => preserves _ (checked row member)

/-- Identical assertion and lookup systems have identical constraints on retained rows. -/
theorem withComponent_constraints
    (constraints : component.operations.constraints = table.component.operations.constraints)
    (lookups : component.operations.lookups = table.component.operations.lookups) :
    (table.withComponent component width fixed name inputWidth).Constraints ↔ table.Constraints := by
  simp only [Constraints, withComponent, environment, Operations.ConstraintsHold, constraints, lookups]

/-- Equal channel operations retain every interaction occurrence in its original order. -/
theorem withComponent_interactions (channel : RawChannel F)
    (same : component.operations.interactionsWith channel = table.component.operations.interactionsWith channel) :
    (table.withComponent component width fixed name inputWidth).interactionsWith channel =
      table.interactionsWith channel := by
  simp only [interactionsWith, withComponent, environment, Operations.interactionValuesWith, same]

/-- Channel guarantees transport at the same data, without assuming projected balance. -/
theorem withComponent_channelGuarantees_of (channel : RawChannel F)
    (preserves : ∀ env, table.component.operations.ChannelGuarantees channel env →
      component.operations.ChannelGuarantees channel env)
    (guarantees : table.ChannelGuarantees channel) :
    (table.withComponent component width fixed name inputWidth).ChannelGuarantees channel :=
  fun row member => preserves _ (guarantees row member)

end Table

/-- A replacement with the same name and derived entries preserves the complete data function. -/
theorem deriveTables_set (tables : List (Table F)) (index : Fin tables.length)
    (replacement : Table F)
    (name : replacement.component.circuit.name = tables[index.val].component.circuit.name)
    (entries : ∀ arity, replacement.rowPrefixes arity = tables[index.val].rowPrefixes arity) :
    deriveTables (tables.set index.val replacement) = deriveTables tables := by
  induction tables with
  | nil => exact Fin.elim0 index
  | cons table tables ih =>
    rcases index with ⟨index, bound⟩
    cases index with
    | zero =>
      funext key arity
      simp only [List.set_cons_zero, deriveTables, List.getElem_cons_zero] at name entries ⊢
      rw [name]
      split
      · exact entries arity
      · rfl
    | succ index =>
      have tail := ih ⟨index, by simpa using bound⟩ name entries
      funext key arity
      simp only [List.set_cons_succ, deriveTables, tail]

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Replacing a table by one with the same named rows and data preserves canonicality. -/
theorem EnsembleWitness.same_data_set {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (index : Fin witness.tables.length) (replacement : Table F)
    (name : replacement.component.circuit.name = witness.tables[index.val].component.circuit.name)
    (entries : ∀ arity, replacement.rowPrefixes arity = witness.tables[index.val].rowPrefixes arity)
    (data : replacement.data = witness.data) :
    ∀ table ∈ witness.tables.set index.val replacement,
      table.data = deriveProverData (witness.tables.set index.val replacement)
        (toElements witness.publicInput).toArray := by
  have derived : deriveProverData (witness.tables.set index.val replacement)
      (toElements witness.publicInput).toArray = witness.data := by
    simp only [deriveProverData, deriveTables_set witness.tables index replacement name entries,
      EnsembleWitness.data]
  rw [derived]
  intro table member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact witness.same_data table old
  · exact data

/-- Replace a registered component, retaining its unique data key. -/
def Ensemble.replaceComponent (ens : Ensemble F PublicIO) {component : Component F}
    (slot : TableSlot ens.tables component) (replacement : Component F)
    (name : replacement.circuit.name = component.circuit.name)
    (registered : replacement.circuit.channels ⊆ ens.channels) : Ensemble F PublicIO :=
  { ens with
    tables := ens.tables.set slot.index.val replacement
    unique_names := by
      rw [List.map_set, name, ← congrArg (fun c : Component F => c.circuit.name) slot.component_eq,
        ← List.getElem_map (l := ens.tables) (f := fun c => c.circuit.name), List.set_getElem_self]
      · exact ens.unique_names
      · simp
    tables_channels := by
      intro table member
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact ens.tables_channels table old
      · exact registered }

end Air.Flat
