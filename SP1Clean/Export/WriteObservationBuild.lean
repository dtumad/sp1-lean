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
    (registered : suffix.map (·.component) = tables source target) :
    EnsembleWitness (preprocessing image source target final) :=
  (appended image source target final).extend (installSources original) suffix registered

theorem build_publicInput (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map Table.component = tables source target) :
    (build w suffix registered).publicInput = w.publicInput :=
  ((appended image source target final).extend_publicInput (installSources w) suffix registered).trans
    (installSources_publicInput w)

theorem build_heights (original : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source target) :
    (build original suffix registered).heights = original.heights ++ suffix.map (·.length) := by
  change ((appended image source target final).extend _ _ _).heights = _
  rw [Ensemble.AppendedTables.extend_heights]
  exact congrArg (fun hs => hs ++ suffix.map (·.length)) ((sameRows image source target final).symm.heights original)

theorem build_ledger (original : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source target) (ch : RawChannel F) :
    (build original suffix registered).interactionsWith ch =
      (installSources original).interactionsWith ch ++ suffix.flatMap (·.interactionsWith ch) :=
  (appended image source target final).extend_ledger _ suffix registered ch

/-- Every suffix row uses its local circuit assertions and structural channels. -/
theorem suffix_lookupFree (source target : ExecutionSnapshot) : LookupFree (tables source target) := by
  let rest := (tables source target).drop 7
  change LookupFree (ReadbackSupply.component :: WriteProbe.component :: WritePacket.component ::
    WriteBuffer.spanComponent :: WriteBuffer.wordComponent :: WriteEffects.requestComponent :: WriteEffects.wordComponent :: rest)
  simp only [LookupFree.cons_iff]
  refine ⟨Counted.supply_lookupFree, Counted.probe_lookupFree, ?_, ?_, ?_, ?_, ?_, effect_lookupFree source target⟩
  all_goals apply Component.lookups_eq_nil_of_main; intro input offset
  · exact Guarded.main_lookups WritePacket.circuit WritePacket.guardSupported input offset
  · exact Guarded.main_lookups WriteBuffer.spanCircuit WriteBuffer.spanGuardSupported input offset
  · exact Guarded.main_lookups WriteBuffer.stepCircuit WriteBuffer.stepGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.requestCircuit WriteEffects.requestGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.wordCircuit WriteEffects.wordGuardSupported input offset

theorem build_constraints (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (registered : suffix.map (·.component) = tables source target) (prior : w.Constraints)
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

/-- The canonical read-back protocol, including the supplier row block, is the original
source ledger up to permutation of the two groups. -/
theorem installed_readback_perm (w : EnsembleWitness (base image source target final)) (supply : Table F) :
    ((installSources w).interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw).Perm
      (AccessInventory.ledger (raw w) (raw_registered w) supply) := by
  simpa only [AccessInventory.ledger, List.flatMap_cons, List.flatMap_map] using
    (List.perm_append_comm.trans ((installed_sources w).append_left (supply.interactionsWith readbackChannel.toRaw)))

end SP1Clean.Export.WriteObservationAssembly
