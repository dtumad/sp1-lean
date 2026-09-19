import Clean.Air.FlatEnsemble
import Clean.Circuit.WitnessExport

/-! # Exporting complete flat ensembles

## Gap against upstream

Clean exports one circuit's witness operations but omits ensemble membership, public verifier,
channel inventory, and the concrete realization of lookup predicates. `EnsembleExport` supplies
those data together with proofs that every lookup and channel in the ensemble is represented.
A lookup cannot be exported merely by attaching rows to its name: `FiniteLookup` requires that
membership in those rows is equivalent to the original predicate for every prover-data array.

Component lowering reuses Clean's proved flattening and row-operation laws. JSON serialization
and external interpretation remain implementation boundaries; the theorems here concern the typed
Lean representation. The Rust reference consumer currently instantiates prime-field arithmetic.
-/

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- A concrete, prover-data-independent realization of a lookup predicate. -/
structure FiniteLookup (F : Type) where
  table : RawTable F
  rows : List (Vector F table.arity)
  realizes : ∀ data row, table.Contains data row ↔ row ∈ rows

omit [FiniteField F] in
private theorem staticTable_realizes {Row : TypeMap} [ProvableType Row]
    (table : StaticTable F Row) (data : Array (Vector F (size Row))) (row : Vector F (size Row)) :
    table.toTable.toRaw.Contains data row ↔
      row ∈ List.ofFn (fun index => toElements (table.row index)) := by
  change (∃ index, fromElements row = table.row index) ↔ _
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨index, equal⟩
    exact ⟨index, by simpa only [ProvableType.toElements_fromElements]
      using (congrArg toElements equal).symm⟩
  · rintro ⟨index, equal⟩
    exact ⟨index, by rw [← equal, ProvableType.fromElements_toElements]⟩

/-- Static tables have a canonical finite realization; no witness-provided rows are trusted. -/
def FiniteLookup.ofStatic {Row : TypeMap} [ProvableType Row] (table : StaticTable F Row) :
    FiniteLookup F where
  table := table.toTable.toRaw
  rows := List.ofFn (fun index => toElements (table.row index))
  realizes := staticTable_realizes table

/-- Native row operations, with virtual subcircuit boundaries flattened for export. -/
def Component.exportOperations (component : Component F) : List (FlatOperation F) :=
  component.rowOperations.toFlat

/-- Lowering preserves all assertions and lookup constraints of the original component. -/
theorem Component.export_constraints_iff (component : Component F) (env : Environment F) :
    ConstraintsHoldFlat env component.exportOperations ↔ component.operations.ConstraintsHold env := by
  rw [exportOperations, Circuit.constraintsHold_toFlat_iff, component.constraintsHold_iff]

/-- Lowering preserves the complete interaction list, including zero-multiplicity operations. -/
theorem Component.export_interactions (component : Component F) :
    FlatOperation.interactions component.exportOperations = component.operations.interactions := by
  rw [exportOperations, Operations.interactions_toFlat, component.interactions_eq]

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The export inventory is checked against the ensemble itself. Names must identify a unique
component, channel, or fixed table within their respective namespaces. -/
structure EnsembleExport (ens : Ensemble F PublicIO) where
  componentNames : List String
  names_length : componentNames.length = ens.tables.length
  verifierName : String
  names_unique : (verifierName :: componentNames).Nodup
  names_nonempty : ∀ name ∈ verifierName :: componentNames, name ≠ ""
  channels_unique : (ens.channels.map RawChannel.name).Nodup
  channels_nonempty : ∀ channel ∈ ens.channels, channel.name ≠ ""
  lookups : List (FiniteLookup F)
  lookups_unique : (lookups.map (fun lookup => lookup.table.name)).Nodup
  lookups_nonempty : ∀ lookup ∈ lookups, lookup.table.name ≠ ""
  lookups_complete : ∀ component ∈ ens.allTables, ∀ lookup ∈ component.rowOperations.lookups,
    ∃ fixed ∈ lookups, fixed.table = lookup.table
  channels_complete : ∀ component ∈ ens.allTables,
    ∀ interaction ∈ component.rowOperations.interactions, interaction.channel ∈ ens.channels

/-- Executable fixed-table membership after erasing the dependent row type and lookup predicate.
Only the exported name and concrete field array remain. -/
def EnsembleExport.containsFixed [DecidableEq F] {ens : Ensemble F PublicIO}
    (description : EnsembleExport ens) (name : String) (entry : Array F) : Bool :=
  description.lookups.any (fun fixed => fixed.table.name == name &&
    fixed.rows.any (fun row => row.toArray == entry))

/-- Executable channel selection using the exported name rather than equality of Lean
channel records, whose guarantees and requirements are arbitrary propositions. -/
def Component.exportInteractionsNamed (component : Component F) (name : String) :
    List (AbstractInteraction F) :=
  (FlatOperation.interactions component.exportOperations).filter (fun interaction =>
    interaction.channel.name == name)

/-- The name selected by an external checker identifies exactly the original Clean channel.
No interaction is dropped, including those with zero multiplicity. -/
theorem EnsembleExport.interactionsNamed_eq {ens : Ensemble F PublicIO}
    (description : EnsembleExport ens) {component : Component F} (member : component ∈ ens.allTables)
    {channel : RawChannel F} (registered : channel ∈ ens.channels) :
    component.exportInteractionsNamed channel.name = component.operations.interactionsWith channel := by
  classical
  rw [Component.exportInteractionsNamed, component.export_interactions,
    Operations.interactionsWith, component.interactions_eq]
  apply List.filter_congr
  intro interaction used
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact ⟨List.inj_on_of_nodup_map description.channels_unique
    (description.channels_complete component member interaction used) registered,
    congrArg RawChannel.name⟩

/-- Name-based finite lookup evaluation agrees with the original Clean predicate for every
lookup in the ensemble and every prover environment. Unique names prevent substituting a table
with a different membership predicate. -/
theorem EnsembleExport.containsFixed_iff [DecidableEq F] {ens : Ensemble F PublicIO}
    (description : EnsembleExport ens) {component : Component F} (member : component ∈ ens.allTables)
    {lookup : Lookup F} (used : lookup ∈ component.rowOperations.lookups) (env : Environment F) :
    description.containsFixed lookup.table.name (lookup.entry.map env).toArray = true ↔
      lookup.Contains env := by
  obtain ⟨fixed, fixedMem, tableEq⟩ := description.lookups_complete component member lookup used
  rcases lookup with ⟨table, entry⟩
  cases tableEq
  change description.containsFixed fixed.table.name (entry.map env).toArray = true ↔
    fixed.table.Contains (env.data fixed.table.name fixed.table.arity) (entry.map env)
  rw [fixed.realizes]
  simp only [containsFixed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨selected, selectedMem, nameEq, row, rowMem, rowEq⟩
    have selectedEq := List.inj_on_of_nodup_map description.lookups_unique selectedMem fixedMem nameEq
    subst selected
    rw [Vector.toArray_inj.mp rowEq] at rowMem
    exact rowMem
  · intro member
    exact ⟨fixed, fixedMem, rfl, entry.map env, member, rfl⟩

variable [Lean.ToJson F] [DecidableEq F] [Hashable F]

private def componentJson (name : String) (component : Component F) : Except String Lean.Json := do
  let program ← component.rowOperations.witgenJsonShared?
  return Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("inputWidth", Lean.toJson (size component.Input)),
    ("program", program)]

/-- Serialize the complete instance. Unexportable witness closures fail through Clean's existing
operation serializer. The fixed rows come from the proved realization, never from prover data. -/
def EnsembleExport.toJson? {ens : Ensemble F PublicIO} (description : EnsembleExport ens)
    (modulus : ℕ) [CharP F modulus] :
    Except String Lean.Json := do
  let components ← (description.componentNames.zip ens.tables).mapM (fun (name, component) =>
    componentJson name component)
  let verifier ← componentJson description.verifierName ens.verifierTable
  let channels := ens.channels.map (fun channel => Lean.Json.mkObj [
    ("name", Lean.toJson channel.name), ("width", Lean.toJson channel.arity)])
  let lookups := description.lookups.map (fun lookup => Lean.Json.mkObj [
    ("name", Lean.toJson lookup.table.name), ("width", Lean.toJson lookup.table.arity),
    ("rows", Lean.toJson (lookup.rows.map Vector.toArray))])
  return Lean.Json.mkObj [
    ("version", Lean.toJson (1 : ℕ)),
    ("modulus", Lean.toJson modulus),
    ("components", Lean.toJson components),
    ("verifier", verifier),
    ("channels", Lean.toJson channels),
    ("fixedTables", Lean.toJson lookups)]

end Air.Flat
