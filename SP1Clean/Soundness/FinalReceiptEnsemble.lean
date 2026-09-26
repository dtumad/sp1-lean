import SP1Clean.Native.Operations.FinalMemoryReceipt
import ToClean.Air.EnsembleProjection
import ToClean.Air.TableSlot
import ToClean.Air.Footprint
import ToClean.Circuit.InteractionRecovery

/-! # Publishing the physical final inventory

The selected finalizer keeps its complete physical rows and original circuit checks. The
only new interaction is a unit receipt for its original output, including address, value,
and clock. Projection preserves every old channel when the receipt channel is fresh.

This is an installation adapter, not an endpoint theorem. A final assembly must install
consumers on the registered receipt channel; balance then accounts for every finalizer row.
Target-check Byte demand must separately be included in that assembly's Byte closure.
-/

namespace SP1Clean.Soundness.FinalReceiptEnsemble

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime]
  {PublicIO Input : TypeMap} [ProvableType PublicIO] [ProvableType Input]

/-- Publish one full record per row at the selected finalizer and register its receipt channel. -/
def install (ens : Ensemble (ZMod p) PublicIO) (index : Fin ens.tables.length)
    (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg) :
    Ensemble (ZMod p) PublicIO :=
  { ens with
    tables := ens.tables.set index.val ⟨FinalMemoryReceipt.circuit ram provider⟩
    channels := ens.channels ++ [(FinalMemoryValue.channel ram).toRaw] }

variable {ens : Ensemble (ZMod p) PublicIO} {index : Fin ens.tables.length}
  {ram : Bool} {provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg}

/-- The replaced table exists in the physical witness. -/
theorem bound (witness : EnsembleWitness (install ens index ram provider)) :
    index.val < witness.tables.length := by
  rw [← witness.same_length]
  simpa only [install, List.length_set] using index.isLt

/-- Register the installed receipt-bearing finalizer at its original physical position. -/
def slot : TableSlot (install ens index ram provider).tables
    ⟨FinalMemoryReceipt.circuit ram provider⟩ where
  index := ⟨index.val, by simpa only [install, List.length_set] using index.isLt⟩
  component_eq := List.getElem_set_self (by simpa only [install, List.length_set] using index.isLt)

/-- Read the original physical table through its registered receipt-producing component. -/
def table (witness : EnsembleWitness (install ens index ram provider)) : Table (ZMod p) :=
  slot.table witness

theorem table_component (witness : EnsembleWitness (install ens index ram provider)) :
    (table witness).component = ⟨FinalMemoryReceipt.circuit ram provider⟩ := by
  exact slot.table_component witness

/-- Forget the receipt while retaining the row arrays, shared data, and public input. -/
def project (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness (install ens index ram provider)) : EnsembleWitness ens :=
  EnsembleWitness.ofTables ens
    (witness.tables.set index.val ((table witness).withComponent ⟨provider⟩))
    witness.data witness.publicInput
    (by
      rw [List.map_set, witness.tables_map_component]
      change (ens.tables.set index.val _).set index.val ⟨provider⟩ = ens.tables
      rw [List.set_set, ← same, List.set_getElem_self])
    (by
      intro physical member
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact witness.same_data physical old
      · change (table witness).data = witness.data
        exact witness.same_data _ (List.getElem_mem _))

/-- Projection changes only the selected table's component. -/
theorem project_tables (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness (install ens index ram provider)) :
    (project same witness).tables =
      witness.tables.set index.val ((table witness).withComponent ⟨provider⟩) := rfl

/-- Construct the receipt-bearing witness from the original arrays, without new witness data. -/
def lift (witness : EnsembleWitness ens) : EnsembleWitness (install ens index ram provider) :=
  EnsembleWitness.ofTables (install ens index ram provider)
    (witness.tables.set index.val
      ((witness.tables[index.val]'(by rw [← witness.same_length]; exact index.isLt)).withComponent
        ⟨FinalMemoryReceipt.circuit ram provider⟩)) witness.data witness.publicInput
    (by rw [List.map_set, witness.tables_map_component]; rfl)
    (by
      intro physical member
      rcases List.mem_or_eq_of_mem_set member with old | rfl
      · exact witness.same_data physical old
      · change (witness.tables[index.val]'_).data = witness.data
        exact witness.same_data _ (List.getElem_mem _))

/-- Constructing and then forgetting a receipt returns the original physical tables exactly. -/
theorem project_lift_tables (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness ens) :
    (project same (lift (ram := ram) witness)).tables = witness.tables := by
  rw [project_tables]
  simp only [lift, EnsembleWitness.ofTables_tables, table, TableSlot.table, slot, List.getElem_set_self]
  have component : (witness.tables[index.val]'(by rw [← witness.same_length]; exact index.isLt)).component =
      ⟨provider⟩ := by rw [← witness.same_circuits index.val index.isLt, same]
  rw [show ((witness.tables[index.val]'_).withComponent
        ⟨FinalMemoryReceipt.circuit ram provider⟩).withComponent ⟨provider⟩ =
      witness.tables[index.val]'_ by rw [← component]; rfl,
    List.set_set, List.set_getElem_self]

/-- Publishing receipts changes no row constraints, in either direction. -/
theorem project_constraints (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness (install ens index ram provider)) :
    (project same witness).Constraints ↔ witness.Constraints := by
  have selected : ((table witness).withComponent ⟨provider⟩).Constraints ↔
      (table witness).Constraints :=
    Table.withComponent_constraints _ _
      (by rw [table_component, FinalMemoryReceipt.constraints])
      (by rw [table_component, FinalMemoryReceipt.lookups])
  simp only [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  constructor
  · rintro ⟨verifier, tables⟩
    refine ⟨verifier, ?_⟩
    intro physical member
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp member
    rw [project_tables] at tables
    by_cases equal : j = index.val
    · subst j
      apply selected.mp
      apply tables
      exact List.mem_iff_getElem.mpr ⟨index.val, by simpa using bound witness,
        List.getElem_set_self (by simpa using bound witness)⟩
    · apply tables
      exact List.mem_iff_getElem.mpr ⟨j, by simpa using hj,
        List.getElem_set_ne (Ne.symm equal) _⟩
  · rintro ⟨verifier, tables⟩
    refine ⟨verifier, ?_⟩
    intro physical member
    rw [project_tables] at member
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · exact tables physical old
    · exact selected.mpr (tables _ (List.getElem_mem _))

/-- Existing generated rows satisfy the installed constraints with no new constructor premise. -/
theorem lift_constraints (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness ens) (checked : witness.Constraints) :
    (lift (index := index) (ram := ram) (provider := provider) witness).Constraints := by
  apply (project_constraints same (lift witness)).mp
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  refine ⟨checked witness.verifierTable witness.mem_allTables_verifierTable, ?_⟩
  rw [project_lift_tables same witness]
  exact fun physical member => checked physical (witness.mem_allTables_of_mem_tables member)

/-- Projection preserves every table height, including the singleton verifier. -/
theorem project_tableHeights (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness (install ens index ram provider)) :
    (project same witness).tableHeights = witness.tableHeights := by
  change _ :: ((project same witness).tables.map Table.length) =
    _ :: (witness.tables.map Table.length)
  congr 1
  rw [project_tables, List.map_set]
  change (witness.tables.map Table.length).set index.val
    ((witness.tables[index.val]'(bound witness)).length) = _
  rw [← List.getElem_map (l := witness.tables) (i := index.val) (f := Table.length),
    List.set_getElem_self]
  simpa only [List.length_map] using bound witness

/-- Every occurrence on every other channel is unchanged, including disabled occurrences. -/
theorem project_interactions (same : ens.tables[index.val] = ⟨provider⟩)
    (witness : EnsembleWitness (install ens index ram provider)) (channel : RawChannel (ZMod p))
    (different : channel ≠ (FinalMemoryValue.channel ram).toRaw) :
    (project same witness).interactionsWith channel = witness.interactionsWith channel := by
  have row := Table.withComponent_interactions (table witness) ⟨provider⟩ channel
    (by rw [table_component, FinalMemoryReceipt.interactions ram provider channel different])
  change witness.verifierTable.interactionsWith channel ++
      (witness.tables.set index.val _).flatMap (·.interactionsWith channel) =
    witness.verifierTable.interactionsWith channel ++ witness.tables.flatMap (·.interactionsWith channel)
  congr 1
  rw [List.flatMap, List.map_set, row]
  change ((witness.tables.map (fun physical => physical.interactionsWith channel)).set index.val
    ((witness.tables[index.val]'(bound witness)).interactionsWith channel)).flatten = _
  rw [← List.getElem_map (l := witness.tables) (i := index.val)
    (f := fun physical : Table (ZMod p) => physical.interactionsWith channel), List.set_getElem_self]
  · rfl
  · simpa only [List.length_map] using bound witness

/-- A fresh receipt channel permits reuse of the original ensemble balance proof. -/
theorem project_balanced (same : ens.tables[index.val] = ⟨provider⟩)
    (fresh : (FinalMemoryValue.channel ram).toRaw ∉ ens.channels)
    (witness : EnsembleWitness (install ens index ram provider))
    (balanced : witness.BalancedChannels) : (project same witness).BalancedChannels := by
  intro channel member
  change BalancedInteractions ((project same witness).interactionsWith channel)
  rw [project_interactions same witness channel (by rintro rfl; exact fresh member)]
  exact balanced channel (List.mem_append_left _ member)

/-- The inventory is decoded from the original provider output on the literal physical rows. -/
def records (witness : EnsembleWitness (install ens index ram provider)) : List (MemoryMsg (ZMod p)) :=
  (table witness).table.map fun row => (⟨provider⟩ : Component (ZMod p)).rowOutput
    ((table witness).environment row)

/-- If the original provider is silent on the receipt channel, every finalizer row publishes
exactly one of its complete original records. -/
theorem table_receipts (witness : EnsembleWitness (install ens index ram provider))
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    (table witness).interactionsWith (FinalMemoryValue.channel ram).toRaw =
      (records witness).map (FinalMemoryValue.channel ram).pushedValue := by
  have row (env : Environment (ZMod p)) :
      (⟨FinalMemoryReceipt.circuit ram provider⟩ : Component (ZMod p)).operations.interactionValuesWith
        (FinalMemoryValue.channel ram).toRaw env =
      [(FinalMemoryValue.channel ram).pushedValue ((⟨provider⟩ : Component (ZMod p)).rowOutput env)] := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    rw [FinalMemoryReceipt.receipt_interactions]
    rw [InteractionRecovery.interactionsWith_main_eq_nil provider.base _ _ _ silent]
    simp only [List.nil_append, List.map_cons, List.map_nil, Channel.eval_pushed]
    rfl
  simp only [Table.interactionsWith, table_component, row, records, List.map_map]
  exact List.map_eq_flatMap.symm

/-- The receipt channel costs exactly one physical occurrence per finalizer row. -/
theorem table_receipts_length (witness : EnsembleWitness (install ens index ram provider))
    (silent : (FinalMemoryValue.channel ram).toRaw ∉ provider.channels) :
    ((table witness).interactionsWith (FinalMemoryValue.channel ram).toRaw).length =
      (table witness).length := by
  rw [table_receipts witness silent, List.length_map]
  exact List.length_map _

end SP1Clean.Soundness.FinalReceiptEnsemble
