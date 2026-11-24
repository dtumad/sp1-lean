import SP1Clean.Export.WriteObservationProjection
import SP1Clean.Export.WriteSourceLedger
import ToClean.Air.AppendedTables

/-! # Recovering the genuine source of a physically installed WRITE version

The original supervisor and its complete State and Memory ledgers are retained. The whole
read-back channel consists of its 31 original source tables and the installed counted supplier.
Raw LogUp acceptance supplies both balance and the characteristic bound.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe WriteProbe.AccessInventory WriteSourceRegistry Soundness

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

/-- The packet and host circuit tables form an actual suffix after the decorated supervisor. -/
theorem appended : Ensemble.AppendedTables (withSources image source target final)
    (preprocessing image source target final) (tables source target) := ⟨rfl, rfl⟩

attribute [local irreducible] base withSources preprocessing

/-- The supplier is the first appended table. -/
def supplySlot : TableSlot (preprocessing image source target final).tables ReadbackSupply.component :=
  slot image source target final 0

private theorem supply_position :
    (supplySlot image source target final).index.val = (withSources image source target final).tables.length := by
  change _ + 0 = _
  exact Nat.add_zero _

private theorem supervisor_lookupFree : LookupFree (withSources image source target final).tables := by
  apply (sameRows image source target final).lookupFree
  change LookupFree (base image source target final).tables
  unfold base
  exact HostObserved.lookupFree (image := image) (source := source) (target := target) (final := final)

variable {image source target final}

/-- Project away the preprocessing suffix and erase just the extra source publications. -/
def supervisor (w : EnsembleWitness (preprocessing image source target final)) : EnsembleWitness (base image source target final) :=
  WriteSourceRegistry.project ((appended image source target final).project w)

theorem supervisor_constraints (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints) :
    (supervisor w).Constraints :=
  project_constraints ((appended image source target final).project w)
    ((appended image source target final).constraints w (supervisor_lookupFree image source target final) checked)

private theorem silent_of_name {components : List (Component F)} {ch : RawChannel F}
    (absent : ch.name ∉ components.flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    ∀ c ∈ components, ch ∉ c.circuit.channels := by
  intro c member used
  exact absent (List.mem_flatMap.mpr ⟨c, member, List.mem_map_of_mem (f := RawChannel.name) used⟩)

/-- WRITE observation never changes a physical State or Memory occurrence. -/
theorem supervisor_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (protocol : ch = Channels.stateChannel.toRaw ∨ ch = Channels.memoryChannel.toRaw) :
    w.interactionsWith ch = (supervisor w).interactionsWith ch := by
  have absent : ch.name ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name) := by
    rcases protocol with rfl | rfl <;> exact of_decide_eq_true rfl
  have other : ch ≠ readbackChannel.toRaw := by
    rcases protocol with rfl | rfl <;> intro eq <;> exact Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq)
  exact ((appended image source target final).ledger_of_silent w ch (silent_of_name absent)).trans
    (project_ledger _ ch other).symm

/-- The complete installed private ledger is the counted supplier and its genuine original
sources, up to permutation. It includes padded rows even when their multiplicity is zero. -/
theorem readback_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let producers := (appended image source target final).project w
    (w.interactionsWith readbackChannel.toRaw).Perm (AccessInventory.ledger (rawSource producers)
      (rawSource_component producers) ((supplySlot image source target final).table w)) := by
  let install := appended image source target final
  let producers := install.project w
  let supplied := (supplySlot image source target final).table w
  let tail := (tables source target).tail
  have names : (readbackChannel (p := SP1Prime)).name ∉ tail.flatMap (fun c => c.circuit.channels.map RawChannel.name) :=
    of_decide_eq_true rfl
  have split := install.ledger_first w readbackChannel.toRaw (supplySlot image source target final)
    (supply_position image source target final) (rest := tail) rfl (silent_of_name names)
  rw [split]
  have exchanged := List.perm_append_comm (l₁ := producers.interactionsWith readbackChannel.toRaw)
    (l₂ := supplied.interactionsWith readbackChannel.toRaw)
  simpa only [AccessInventory.ledger, List.flatMap_cons, List.flatMap_map] using
    exchanged.trans ((WriteSourceRegistry.readback_ledger producers).append_left (supplied.interactionsWith readbackChannel.toRaw))

/-- Physical capacity counts the supplier and every pull site of each original source. -/
theorem readback_occurrences (w : EnsembleWitness (preprocessing image source target final)) :
    let producers := (appended image source target final).project w
    let supply := (supplySlot image source target final).table w
    (w.interactionsWith readbackChannel.toRaw).length =
      supply.length + (sources.map (fun id => (rawSource producers id).length * perRow (p := SP1Prime) id)).sum :=
  (readback_ledger w).length_eq.trans (ledger_length _ _ _ ((supplySlot image source target final).table_component w))

theorem readback_registered :
    readbackChannel.toRaw ∈ (preprocessing image source target final).channels := by
  let supply := supplySlot image source target final
  have member : ReadbackSupply.component ∈ (preprocessing image source target final).tables :=
    supply.component_eq ▸ List.getElem_mem supply.index.isLt
  apply (preprocessing image source target final).tables_channels _ member
  change _ ∈ [readbackChannel.toRaw, versionChannel.toRaw]
  exact List.mem_cons_self

/-- Every positive counted version names the genuine key, word and time interval in an
original source row. The private source group is determined by this physical witness. -/
theorem authenticates_versions (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (balanced : w.BalancedChannel readbackChannel.toRaw) :
    ((supplySlot image source target final).table w).Authenticates versionChannel
      (Meaning (rawSource ((appended image source target final).project w))) := by
  let supply := supplySlot image source target final
  let producers := (appended image source target final).project w
  exact AccessInventory.authenticates_versions (rawSource producers) (rawSource_component producers)
    (supply.table w) (supply.table_component w) (supply.table_constraints w checked)
    (BalancedInteractions.of_perm balanced (readback_ledger w))

/-- At the public stream checker's entry point, the raw LogUp count bound and balances
authenticate every counted version at its complete set of original physical sources. -/
theorem assembled_versions (w : EnsembleWitness (assembly image source target final))
    (checked : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((supplySlot image source target final).table (observed w)).Authenticates versionChannel
      (Meaning (rawSource ((appended image source target final).project (observed w)))) :=
  authenticates_versions (observed w) ((observed_constraints w).mp checked)
    (observed_balance w fit raw _ readback_registered (of_decide_eq_true rfl))

end SP1Clean.Export.WriteObservationAssembly
