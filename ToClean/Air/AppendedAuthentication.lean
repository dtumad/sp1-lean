module

public import ToClean.Air.AppendedTables
public import ToClean.Air.Authentication

/-! # Authenticating a fresh channel from its installed physical supplier

Clean's table-group balance authenticates records from every table in a supplied group.
For appended channels, the group is determined by the physical suffix, and unique component
names identify the selected source table without an extra witness or a validity assumption.
-/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F] {Public : TypeMap} [ProvableType Public]
  {a b : Ensemble F Public} {extra : List (Component F)}

theorem EnsembleWitness.interactionsWith_nil_of_not_registered (w : EnsembleWitness a)
    (ch : RawChannel F) (absent : ch ∉ a.channels) : w.interactionsWith ch = [] := by
  classical
  rw [w.interactionsWith_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro interaction member
  have separate : interaction.channel ≠ ch := fun eq => absent (eq ▸ EnsembleWitness.channel_mem_of_mem_interactions member)
  simpa using separate

/-- A projected prefix cannot contribute to a freshly appended channel. -/
theorem Ensemble.AppendedTables.fresh_ledger (layout : Ensemble.AppendedTables a b extra)
    (w : EnsembleWitness b) (ch : RawChannel F) (absent : ch ∉ a.channels) :
    w.interactionsWith ch = (w.tables.drop a.tables.length).flatMap (·.interactionsWith ch) := by
  rw [layout.ledger, EnsembleWitness.interactionsWith_nil_of_not_registered _ _ absent, List.nil_append]

/-- Recover a typed pull using the actual selected table's physical source proof.
All other components in the installed suffix may be consumers or silent. -/
theorem Ensemble.AppendedTables.authenticated_pull (layout : Ensemble.AppendedTables a b extra)
    (w : EnsembleWitness b) {Record : TypeMap} [ProvableType Record] (ch : Channel F Record)
    (fresh : ch.toRaw ∉ a.channels) {src : Component F} (slot : TableSlot b.tables src)
    (property : Record F → Prop) (provider : (slot.table w).Authenticates ch property)
    (others : ∀ c ∈ extra, c ≠ src → c.Authenticates ch property)
    (checked : w.Constraints) (balanced : w.BalancedChannel ch.toRaw)
    (r : Record F) (member : ch.pulledValue r ∈ w.interactionsWith ch.toRaw) : property r := by
  have eq := layout.fresh_ledger w ch.toRaw fresh
  apply authenticated_pull_of_tables _ ch property _ (eq ▸ balanced) r (eq ▸ member)
  intro table inSuffix
  have inAll := List.mem_of_mem_drop inSuffix
  by_cases same : table.component = src
  · have names : (w.tables.map (fun t => t.component.circuit.name)).Nodup := by
      simpa only [← w.tables_map_component, List.map_map, Function.comp_def] using b.unique_names
    have equal := List.inj_on_of_nodup_map names inAll (slot.table_mem w)
      (congrArg (fun c => c.circuit.name) (same.trans (slot.table_component w).symm))
    exact equal ▸ provider
  · apply Table.Authenticates.of_component _ _ _ _ (checked table inAll)
    apply others table.component _ same
    rw [← layout.suffix_components w]
    exact List.mem_map_of_mem inSuffix

end Air.Flat
