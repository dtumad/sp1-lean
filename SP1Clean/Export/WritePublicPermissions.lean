import SP1Clean.Export.WriteSupervisorPermissions
import SP1Clean.Export.WriteObservationBuild

/-! # The whole public WRITE verifier's signed byte-permission ledger -/

namespace SP1Clean.Export.WriteMixedPermissionLedger
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WritePermissionProvider WriteSourceRegistry WriteMixedSourceTables
open WriteObservationAssembly
private abbrev F := ZMod SP1Prime
private abbrev bus := (channel (p := SP1Prime)).toRaw

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

/-- Installing read-back receipts, all nineteen observer tables and both public checks
preserves the complete original ledger of native byte-write permissions. -/
theorem public_ledger (w : EnsembleWitness (base image source target finish)) (suffix : List (Table F))
    (registered : suffix.map Table.component = tables source target) :
    (withPublicChecks (build w suffix registered)).interactionsWith bus = w.interactionsWith bus := by
  have original : bus ∈ (base image source target finish).channels := (base image source target finish).tables_channels _
    (List.mem_of_getElem? (WriteMixedFixedResources.registered_at image source target finish (.permission false))) (by
      change _ ∈ (WritePermissionProvider.component image).circuit.channels
      exact List.mem_append_right _ (List.mem_cons_self ..))
  have full : bus ∈ (preprocessing image source target finish).channels := by
    change _ ∈ channels ++ (withSources image source target finish).channels
    rw [channels_eq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ original)
  have quiet : bus.name ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name) := of_decide_eq_true rfl
  have empty : suffix.flatMap (·.interactionsWith bus) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t used
    apply Table.interactionsWith_nil_of_channel_not_mem
    exact fun member => quiet (List.mem_flatMap.mpr ⟨t.component,registered ▸ List.mem_map_of_mem used,List.mem_map_of_mem member⟩)
  rw [withPublicChecks_ledger _ _ full (by decide),build_ledger,empty,List.append_nil,installSources_ledger _ _ (by apply ne_of_apply_ne RawChannel.name; decide)]

/-- Complete signed balance for the one actual permission ledger of the public witness. -/
theorem public_balanced {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedFixedResources.Remaining image source target finish)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target) :
    let host := WriteMixedFixedResources.install run routed data hint packets remaining
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    LogUpBalanced ((withPublicChecks (build w suffix registered)).interactionsWith bus) := by
  intro host w
  rw [public_ledger]
  exact supervisor_balanced run routed data hint packets header remaining

end SP1Clean.Export.WriteMixedPermissionLedger
