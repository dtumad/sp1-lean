import SP1Clean.Export.WriteObservationSources
import SP1Clean.Proofs.Completeness.WriteCountedRouting
import SP1Clean.Proofs.Completeness.WriteCountedData
import SP1Clean.Proofs.Completeness.WriteBufferAssembly
import ToClean.Air.AppendedBuild
import ToClean.Air.MessageFilter

/-! # Installing the source, supply and probe rows at their genuine physical positions

The source data comes from the original supervisor's actual tables. Counted routing emits the
requested reads and closes the raw private channels against those exact physical publications.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe AccessInventory Counted WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base withSources preprocessing

/-- Assemble the complete observer suffix against the actual original supervisor. All arrays
are canonically rebound to the shared public header and full list of tables. -/
def build (original : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source.host target.host) :
    EnsembleWitness (preprocessing image source target final) :=
  (appended image source target final).extend (installSources original) suffix registered

theorem build_heights (original : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source.host target.host) :
    (build original suffix registered).heights = original.heights ++ suffix.map (·.length) := by
  change ((appended image source target final).extend _ _ _).heights = _
  rw [Ensemble.AppendedTables.extend_heights]
  exact congrArg (fun hs => hs ++ suffix.map (·.length)) ((sameRows image source target final).symm.heights original)

theorem build_ledger (original : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source.host target.host) (ch : RawChannel F) :
    (build original suffix registered).interactionsWith ch =
      (installSources original).interactionsWith ch ++ suffix.flatMap (·.interactionsWith ch) :=
  (appended image source target final).extend_ledger _ suffix registered ch

/-- Every suffix row uses its local circuit assertions and structural channels. -/
theorem suffix_lookupFree (s t : HostState) : LookupFree (tables s t) := by
  simp only [tables, LookupFree.cons_iff, LookupFree.nil, and_true]
  refine ⟨Counted.supply_lookupFree, Counted.probe_lookupFree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply Component.lookups_eq_nil_of_main; intro input offset
  · exact Guarded.main_lookups WritePacket.circuit WritePacket.guardSupported input offset
  · exact Guarded.main_lookups WriteBuffer.spanCircuit WriteBuffer.spanGuardSupported input offset
  · exact Guarded.main_lookups WriteBuffer.stepCircuit WriteBuffer.stepGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.requestCircuit WriteEffects.requestGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.wordCircuit WriteEffects.wordGuardSupported input offset
  · rfl
  · exact Guarded.main_lookups WriteEffects.laneCircuit WriteEffects.laneGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.byteStepCircuit WriteEffects.byteStepGuardSupported input offset

theorem build_constraints (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source.host target.host) (prior : w.Constraints)
    (added : ∀ t ∈ suffix, t.Constraints) : (build w suffix registered).Constraints := by
  let placement := appended image source target final
  apply placement.extend_constraints (installSources w) suffix registered _ (installSources_constraints w prior) added
  rw [placement.tables]
  apply LookupFree.append _ (suffix_lookupFree _ _)
  apply (sameRows image source target final).lookupFree
  change LookupFree (base image source target final).tables
  unfold base
  exact Soundness.HostObserved.lookupFree (image := image) (source := source) (target := target) (final := final)

/-- Installation keeps the full original read-back source block, in physical order up to a
permutation of component groups. -/
theorem installed_sources (w : EnsembleWitness (base image source target final)) :
    ((installSources w).interactionsWith readbackChannel.toRaw).Perm (sources.flatMap (fun id =>
      (publish id (raw w id) (raw_registered w id)).interactionsWith readbackChannel.toRaw)) := by
  apply (WriteSourceRegistry.readback_ledger (installSources w)).trans (List.Perm.of_eq ?_)
  apply List.flatMap_congr
  intro id _
  have installed := (publish_project (installSources w) id).trans (installSources_publish w id)
  exact congrArg (fun t : Table F => t.interactionsWith readbackChannel.toRaw) installed

/-- A successful deterministic counted route generates the two physical components and both
of their raw private balances against the real installed supervisor. Coverage and clock bounds
of a generated supervisor are separate compiler obligations. -/
theorem counted_tables (w : EnsembleWitness (base image source target final)) (checked : w.Constraints)
    (bounded : ∀ r ∈ live (AccessInventory.records (raw w)), Bounded r) (reads : List (Read F))
    {requests : List (Request (live (AccessInventory.records (raw w))).length F)}
    (routed : route? (live (AccessInventory.records (raw w))) reads = some requests)
    (data : ProverData F) (supplyFits probeFits) :
    let recs := live (AccessInventory.records (raw w))
    let supply := Counted.table (allocated recs requests) data supplyFits
    let inputs := probes recs requests
    let observer := WriteProbe.table inputs data probeFits
    supply.Constraints ∧ supply.Guarantees ∧ observer.Constraints ∧ observer.Guarantees ∧
      LogUpBalanced ((installSources w).interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw) ∧
      LogUpBalanced (supply.interactionsWith versionChannel.toRaw ++ observer.interactionsWith versionChannel.toRaw) ∧
      inputs.map Inputs.read = reads ∧ inputs.length = reads.length := by
  have valid id : (raw w id).Constraints := (originalSlot image source target final id).table_constraints w checked
  obtain ⟨supply, guarantee, probe, probeGuarantee, incoming, versions, emitted, count⟩ :=
    physical_tables (raw w) (raw_registered w) valid bounded reads routed data supplyFits probeFits
  refine ⟨supply, guarantee, probe, probeGuarantee, ?_, versions, emitted, count⟩
  let table := Counted.table (allocated (live (AccessInventory.records (raw w))) requests) data supplyFits
  have perm : ((installSources w).interactionsWith readbackChannel.toRaw ++ table.interactionsWith readbackChannel.toRaw).Perm
      (AccessInventory.ledger (raw w) (raw_registered w) table) := by
    simpa only [AccessInventory.ledger, List.flatMap_cons, List.flatMap_map] using
      (List.perm_append_comm.trans ((installed_sources w).append_left (table.interactionsWith readbackChannel.toRaw)))
  exact fun msg => (balanceOf_perm perm).trans (incoming msg)

end SP1Clean.Export.WriteObservationAssembly
