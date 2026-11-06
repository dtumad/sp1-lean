import SP1Clean.Native.Operations.FinalMemoryReceipt
import ToClean.Air.ComponentReplacement
import ToClean.Air.Footprint
import ToClean.Circuit.InteractionRecovery

/-! # Publishing the physical final inventory

A typed slot identifies the original finalizer before installing its receipt. The wrapper retains
its name, complete rows, input layout and constraints, and adds one activity-weighted receipt per physical row.
Projection therefore preserves canonical data and every old channel when the receipt is fresh.

The enclosing assembly registers receipt channels with its consumers before installing their
producers, and includes the consumers' Byte demand in its channel-closure proof. Projection
preserves each non-receipt channel; it need not preserve balance on a channel whose producer it removes.
-/

namespace SP1Clean.Soundness.FinalReceiptEnsemble

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime]
  {PublicIO Input : TypeMap} [ProvableType PublicIO] [ProvableType Input]
  {generation : WitnessGeneration.Generation (ZMod p) (ProvablePair Input field)}

private theorem fixedRowsMatch (ram : Bool)
    (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    ({ circuit := provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).FixedRowsMatch =
      ({ circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).FixedRowsMatch := by
  funext rows
  cases generation <;> rfl

/-- Publish one full record at an existing finalizer's registered physical position. -/
def install (ens : Ensemble (ZMod p) PublicIO) (ram : Bool)
    (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg)
    (source : TableSlot ens.tables { circuit := provider, generation, Assumptions := provider.Assumptions })
    (receiptRegistered : (FinalMemoryValue.channel ram).toRaw ∈ ens.channels) :
    Ensemble (ZMod p) PublicIO :=
  ens.replaceComponent source
    { circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions }
    rfl (by
      intro selected member
      have registeredProvider := ens.tables_channels _ (List.getElem_mem source.index.isLt)
      rw [source.component_eq] at registeredProvider
      have parts : selected ∈ provider.channels ∨ selected = (FinalMemoryValue.channel ram).toRaw := by
        change selected ∈ provider.channelsWithGuarantees ++
          (provider.channelsWithRequirements ++ [(FinalMemoryValue.channel ram).toRaw]) at member
        simpa only [GeneralFormalCircuit.channels, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, or_assoc] using member
      exact parts.elim (fun h => registeredProvider h) (fun h => h.symm ▸ receiptRegistered))

variable {ens : Ensemble (ZMod p) PublicIO} {ram : Bool}
  {receiptRegistered : (FinalMemoryValue.channel ram).toRaw ∈ ens.channels}
  {provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg}
  {source : TableSlot ens.tables { circuit := provider, generation, Assumptions := provider.Assumptions }}

/-- The receipt-bearing component occupies exactly the original slot. -/
def slot : TableSlot (install ens ram provider source receiptRegistered).tables
    { circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions } where
  index := ⟨source.index.val, by simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt⟩
  component_eq := List.getElem_set_self (by simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt)

variable (witness : EnsembleWitness (install ens ram provider source receiptRegistered))

theorem bound : source.index.val < witness.tables.length := by
  rw [← witness.same_length]
  simpa only [install, Ensemble.replaceComponent, List.length_set] using source.index.isLt

/-- Read the receipt-producing physical table without rebuilding its rows. -/
def table : Table (ZMod p) := slot.table witness

theorem table_component : (table witness).component = { circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions } :=
  slot.table_component witness

/-- Forget the receipt while retaining every physical row and the public input. -/
def project : EnsembleWitness ens :=
  EnsembleWitness.ofCanonicalTables ens
    (witness.tables.set source.index.val ((table witness).withComponent { circuit := provider, generation, Assumptions := provider.Assumptions }
      (by rw [table_component]; rfl)
      (by rw [table_component]; exact fixedRowsMatch ram provider) (by rw [table_component]; rfl) (by rw [table_component])))
    witness.publicInput (by
      rw [List.map_set, Table.withComponent_component, witness.tables_map_component]
      change (ens.tables.set source.index.val _).set source.index.val { circuit := provider, generation, Assumptions := provider.Assumptions } = ens.tables
      rw [List.set_set]
      simpa only [source.component_eq] using List.set_getElem_self source.index.isLt) (by
      apply witness.same_data_set ⟨source.index.val, bound witness⟩
      · change provider.name = (table witness).component.circuit.name
        rw [table_component]; rfl
      · intro arity; rfl
      · exact witness.same_data (table witness) (slot.table_mem witness))

/-- The wrapper's name and derived input entries agree at every arity. -/
@[simp] theorem project_data : (project witness).data = witness.data := by
  change deriveProverData _ _ = deriveProverData _ _
  unfold deriveProverData
  congr 1
  apply deriveTables_set witness.tables ⟨source.index.val, bound witness⟩
  · change provider.name = (table witness).component.circuit.name
    rw [table_component]
    rfl
  · intro arity
    rfl

@[simp] theorem project_publicInput : (project witness).publicInput = witness.publicInput := rfl

/-- Only the selected table's component changes. -/
theorem project_tables : (project witness).tables =
    witness.tables.set source.index.val ((table witness).withComponent { circuit := provider, generation, Assumptions := provider.Assumptions }
      (by rw [table_component]; rfl)
      (by rw [table_component]; exact fixedRowsMatch ram provider) (by rw [table_component]; rfl) (by rw [table_component])) := rfl

/-- Reuse the original rows when installing the receipt; the typed slot supplies the layout. -/
def lift (witness : EnsembleWitness ens) : EnsembleWitness (install ens ram provider source receiptRegistered) :=
  EnsembleWitness.ofCanonicalTables (install ens ram provider source receiptRegistered)
    (witness.tables.set source.index.val ((source.table witness).withComponent
      { circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions }
      (by rw [source.table_component]; rfl)
      (by rw [source.table_component]; exact (fixedRowsMatch ram provider).symm) (by rw [source.table_component]; rfl) (by rw [source.table_component])))
    witness.publicInput (by rw [List.map_set, Table.withComponent_component, witness.tables_map_component]; rfl) (by
      apply witness.same_data_set ⟨source.index.val, by rw [← witness.same_length]; exact source.index.isLt⟩
      · change (FinalMemoryReceipt.circuit ram provider).name = (source.table witness).component.circuit.name
        rw [source.table_component]; rfl
      · intro arity; rfl
      · exact witness.same_data (source.table witness) (source.table_mem witness))

@[simp] theorem lift_data (witness : EnsembleWitness ens) :
    (lift (source := source) (ram := ram) (receiptRegistered := receiptRegistered) witness).data = witness.data := by
  change deriveProverData _ _ = deriveProverData _ _
  unfold deriveProverData
  congr 1
  apply deriveTables_set witness.tables ⟨source.index.val, by rw [← witness.same_length]; exact source.index.isLt⟩
  · change (FinalMemoryReceipt.circuit ram provider).name = (source.table witness).component.circuit.name
    rw [source.table_component]
    rfl
  · intro arity
    rfl

/-- Constructing and forgetting a receipt returns the complete original physical inventory. -/
theorem project_lift_tables (witness : EnsembleWitness ens) :
    (project (lift (source := source) (ram := ram) (receiptRegistered := receiptRegistered) witness)).tables = witness.tables := by
  have undo : (table (lift (source := source) (ram := ram) (receiptRegistered := receiptRegistered) witness)).withComponent
      { circuit := provider, generation, Assumptions := provider.Assumptions } (by rw [table_component]; rfl)
      (by rw [table_component]; exact fixedRowsMatch ram provider) (by rw [table_component]; rfl) (by rw [table_component]) =
      source.table witness := by
    rw [Table.ext_iff]
    constructor
    · exact (source.table_component witness).symm
    · have lifted : table (lift (source := source) (ram := ram) (receiptRegistered := receiptRegistered) witness) =
          (source.table witness).withComponent { circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions }
            (by rw [source.table_component]; rfl)
            (by rw [source.table_component]; exact (fixedRowsMatch ram provider).symm) (by rw [source.table_component]; rfl) (by rw [source.table_component]) :=
        List.getElem_set_self (by simpa only [List.length_set, ← witness.same_length] using source.index.isLt)
      have rows := congrArg (fun physical : Table (ZMod p) => physical.table) lifted
      have data := congrArg (fun physical : Table (ZMod p) => physical.data) lifted
      exact ⟨rows, data⟩
  change (witness.tables.set source.index.val _).set source.index.val _ = witness.tables
  rw [List.set_set, undo]
  exact List.set_getElem_self _

/-- Receipt publication preserves both assertions and lookups on every row. -/
theorem project_constraints : (project witness).Constraints ↔ witness.Constraints := by
  have selected := Table.withComponent_constraints (table witness) { circuit := provider, generation, Assumptions := provider.Assumptions }
    (by rw [table_component]; rfl)
      (by rw [table_component]; exact fixedRowsMatch ram provider) (by rw [table_component]; rfl) (by rw [table_component])
    (by rw [table_component]; exact (FinalMemoryReceipt.constraints ram provider).symm)
    (by rw [table_component]; exact (FinalMemoryReceipt.lookups ram provider).symm)
  simp only [EnsembleWitness.Constraints]
  constructor
  · intro tables physical member
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp member
    rw [project_tables] at tables
    by_cases equal : j = source.index.val
    · subst j
      apply selected.mp
      exact tables _ (List.mem_iff_getElem.mpr ⟨source.index.val, by simpa using bound witness,
        List.getElem_set_self (by simpa using bound witness)⟩)
    · exact tables _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj,
        List.getElem_set_ne (Ne.symm equal) _⟩)
  · intro tables physical member
    rw [project_tables] at member
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · exact tables physical old
    · exact selected.mpr (tables _ (List.getElem_mem _))

/-- Existing generated rows need no additional semantic premise to publish receipts. -/
theorem lift_constraints (witness : EnsembleWitness ens) (checked : witness.Constraints) :
    (lift (source := source) (ram := ram) (receiptRegistered := receiptRegistered) witness).Constraints := by
  apply (project_constraints (lift witness)).mp
  rw [EnsembleWitness.Constraints, project_lift_tables]
  exact checked

/-- All original arrays survive projection, including repeated rows. -/
theorem project_rows : (project witness).tables.map (·.table) = witness.tables.map (·.table) := by
  rw [project_tables, List.map_set]
  change (witness.tables.map (·.table)).set source.index.val
    (witness.tables[source.index.val]'(bound witness)).table = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val) (f := fun physical => physical.table),
    List.set_getElem_self]
  simpa only [List.length_map] using bound witness

/-- Receipt publication changes no physical table height. -/
theorem project_heights : (project witness).heights = witness.heights := by
  change ((project witness).tables.map Table.length) = witness.tables.map Table.length
  rw [project_tables, List.map_set]
  change (witness.tables.map Table.length).set source.index.val
    (witness.tables[source.index.val]'(bound witness)).length = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val) (f := Table.length),
    List.set_getElem_self]
  simpa only [List.length_map] using bound witness

/-- Every occurrence on other channels survives, including zero-multiplicity occurrences. -/
theorem project_interactions (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw) :
    (project witness).interactionsWith channel = witness.interactionsWith channel := by
  have row := Table.withComponent_interactions (table witness) { circuit := provider, generation, Assumptions := provider.Assumptions }
    (by rw [table_component]; rfl)
      (by rw [table_component]; exact fixedRowsMatch ram provider) (by rw [table_component]; rfl) (by rw [table_component]) channel
    (by rw [table_component]; exact (FinalMemoryReceipt.interactions ram provider channel different).symm)
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.toTables, Tables.interactionsWith, project_data]
  change ens.verifierOperations.interactionValuesWith channel _ ++
      (witness.tables.set source.index.val _).flatMap (·.interactionsWith channel) =
    ens.verifierOperations.interactionValuesWith channel _ ++
      witness.tables.flatMap (·.interactionsWith channel)
  congr 1
  rw [List.flatMap, List.map_set, row]
  change ((witness.tables.map (fun physical => physical.interactionsWith channel)).set source.index.val
    ((witness.tables[source.index.val]'(bound witness)).interactionsWith channel)).flatten = _
  rw [← List.getElem_map (l := witness.tables) (i := source.index.val)
    (f := fun physical : Table (ZMod p) => physical.interactionsWith channel), List.set_getElem_self]
  · rfl
  · simpa only [List.length_map] using bound witness

/-- Receipt publication retains the provider's guarantees on every original channel. -/
theorem row_channelGuarantees (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw) (env : Environment (ZMod p))
    (guarantees : ({ circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions } :
      Component (ZMod p)).operations.ChannelGuarantees channel env) :
    ({ circuit := provider, generation, Assumptions := provider.Assumptions } :
      Component (ZMod p)).operations.ChannelGuarantees channel env := by
  apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ ?_ env guarantees
  change (provider.instantiate.operations 0).interactionsWith channel ⊆
    ((FinalMemoryReceipt.circuit ram provider).instantiate.operations 0).interactionsWith channel
  rw [FinalMemoryReceipt.interactions ram provider channel different]

/-- Original guarantees survive projection at its identical canonical data. -/
theorem project_channelGuarantees (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw)
    (guarantees : ∀ physical ∈ witness.tables, physical.ChannelGuarantees channel) :
    ∀ physical ∈ (project witness).tables, physical.ChannelGuarantees channel := by
  intro physical member
  rw [project_tables] at member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact guarantees physical old
  · apply Table.withComponent_channelGuarantees_of
    · intro env valid
      apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ ?_ env valid
      rw [table_component]
      change (provider.instantiate.operations 0).interactionsWith channel ⊆
        ((FinalMemoryReceipt.circuit ram provider).instantiate.operations 0).interactionsWith channel
      rw [FinalMemoryReceipt.interactions ram provider channel different]
    · exact guarantees _ (List.getElem_mem _)

/-- Projection retains balance on every channel other than the receipt channel.
The original assembly can already contain receipt consumers, so full balance need not survive. -/
theorem project_balancedChannel (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw)
    (balanced : witness.BalancedChannel channel) : (project witness).BalancedChannel channel := by
  change BalancedInteractions ((project witness).interactionsWith channel)
  rw [project_interactions witness channel different]
  exact balanced

/-- The physical activity expression is the final input field of the provider. -/
def activity : Expression (ZMod p) := (varFromOffset (ProvablePair Input field) 0).2

omit [Fact p.Prime] in
/-- Read the last input column without expanding the provider's complete variable vector. -/
theorem activity_eq : activity (p := p) (Input := Input) = .var ⟨size Input⟩ := by
  simp only [activity, varFromOffset_pair, ProvableType.varFromOffset_field, Nat.zero_add]

/-- Complete physical records retain their multiplicities, including disabled occurrences. -/
def physicalRecords : List (ZMod p × MemoryMsg (ZMod p)) :=
  (table witness).table.map fun row =>
    let env := Environment.fromArray row witness.data
    (env (activity (Input := Input)),
      ({ circuit := provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).rowOutput env)

/-- Semantic records select active rows while retaining the original output and data context. -/
def records : List (MemoryMsg (ZMod p)) :=
  ((table witness).table.filter fun row =>
    decide (Environment.fromArray row witness.data (activity (Input := Input)) = 1)).map fun row =>
      ({ circuit := provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).rowOutput
        (Environment.fromArray row witness.data)

/-- Active record decoding is the Boolean-one projection of the complete physical inventory. -/
theorem records_eq_active_physical : records witness =
    ((physicalRecords witness).filter fun row => decide (row.1 = 1)).map Prod.snd := by
  simp only [records, physicalRecords, List.filter_map, List.map_map, Function.comp_def]

/-- A fresh receipt channel retains one weighted occurrence for every physical finalizer row. -/
theorem table_receipts
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    (table witness).interactionsWith (FinalMemoryValue.channel ram).toRaw =
      (physicalRecords witness).map fun row =>
        (FinalMemoryValue.channel ram).pushedIfValue row.1 row.2 := by
  have row (env : Environment (ZMod p)) :
      ({ circuit := FinalMemoryReceipt.circuit ram provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).operations.interactionValuesWith
        (FinalMemoryValue.channel ram).toRaw env =
      [(FinalMemoryValue.channel ram).pushedIfValue (env (activity (Input := Input)))
        (({ circuit := provider, generation, Assumptions := provider.Assumptions } : Component (ZMod p)).rowOutput env)] := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    rw [FinalMemoryReceipt.receipt_interactions]
    rw [InteractionRecovery.interactionsWith_main_eq_nil provider.base _ _ _ silent]
    simp only [List.nil_append, List.map_cons, List.map_nil, Channel.eval_pushedIf]
    simp only [activity, Component.rowOutput, circuit_norm]
  simp only [Table.interactionsWith, table_component, row, physicalRecords, List.map_map,
    Table.environment, witness.same_data (table witness) (slot.table_mem witness)]
  exact List.map_eq_flatMap.symm

/-- The receipt channel costs exactly one physical occurrence per finalizer row. -/
theorem table_receipts_length
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    ((table witness).interactionsWith (FinalMemoryValue.channel ram).toRaw).length =
      (table witness).length := by
  rw [table_receipts witness silent, List.length_map]
  exact List.length_map _

end SP1Clean.Soundness.FinalReceiptEnsemble
