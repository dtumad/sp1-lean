import SP1Clean.Export.WriteObserverSlotLedger
import SP1Clean.Proofs.Completeness.WriteMetadataTable

/-! # The counted metadata ledger of the installed native WRITE observer -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteSourceRegistry WriteEffects WriteEffects.Witness
private abbrev F := ZMod SP1Prime

/-- The public verifier retains the counted metadata provider, the three reads per dispatch
and the single read per allocation step in their original physical order. -/
theorem installed_metadata_ledger {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
    (w : EnsembleWitness (base image source target final)) (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)
    (provider dispatches nodes : Table F) (atProvider : suffix[7]? = some provider)
    (atDispatch : suffix[8]? = some dispatches) (atNode : suffix[16]? = some nodes) :
    (withPublicChecks (build w suffix reg)).interactionsWith recordChannel.toRaw = Metadata.ledger provider dispatches nodes := by
  let ch := (recordChannel (p := SP1Prime)).toRaw
  change (withPublicChecks (build w suffix reg)).interactionsWith ch = _
  rw [withPublicChecks_ledger _ _ (protocol_installed _ _ _ _ ch record_registered) (by decide),allocation_metadata_ledger]
  simp only [Metadata.ledger,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [build_slot_ledger w suffix reg 7 provider atProvider ch,build_slot_ledger w suffix reg 8 dispatches atDispatch ch,
    build_slot_ledger w suffix reg 16 nodes atNode ch]

end SP1Clean.Export.WriteObservationAssembly
