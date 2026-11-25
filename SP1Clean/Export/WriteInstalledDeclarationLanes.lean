import SP1Clean.Export.InstalledHintRows
import SP1Clean.Export.WriteMixedHostData

/-! # Commitment declarations in the native WRITE observer

The public verifier and observer suffix preserve every physical declaration occurrence on
public and deferred COMMIT rows. The mixed constructor reads those same sixteen tables.
-/
namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry

private abbrev F := ZMod SP1Prime
private abbrev bus := (CommitmentDeclaration.channel (p := SP1Prime)).toRaw
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

attribute [local irreducible] base withSources preprocessing WriteMixedSourceTables.ofExecution

private theorem declaration_registered : bus ∈ (preprocessing image source target finish).channels := by
  unfold preprocessing
  change _ ∈ channels ++ (WriteSourceRegistry.withSources image source target finish).channels
  rw [WriteSourceRegistry.channels_eq]
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  unfold base
  exact HostObserved.declarationsRegistered (image := image) (source := source) (target := target) (final := finish)

/-- An arbitrary public observer witness has declaration occurrences from precisely the
sixteen bank lanes, in physical order. No validity or balance hypothesis is needed. -/
theorem public_declaration_lanes (w : EnsembleWitness (assembly image source target finish)) :
    let lanes := fun deferred => (List.finRange 8).flatMap fun slot =>
      (hintHostTable (observed w) (declarationLane deferred slot)).interactionsWith bus
    w.interactionsWith bus = lanes false ++ lanes true :=
  (observed_ledger w bus declaration_registered (by decide)).symm.trans (declaration_lanes (observed w))

variable {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F)
    (remaining : WriteMixedHostTables.Remaining image source target finish) (packets : List WriteObservations.Packet)
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)

/-- The public declaration ledger equals all physical generated lane ledgers, retaining
padding requests and repeated messages, for any data at the remaining physical slots. -/
theorem installed_declaration_lanes :
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data remaining) packets
    let lanes := fun deferred => (List.finRange 8).flatMap fun slot =>
      (WriteMixedHostTables.table run.1 data (.bank deferred (some slot))).interactionsWith bus
    (withPublicChecks (build w suffix reg)).interactionsWith bus = lanes false ++ lanes true := by
  intro w lanes
  let pre := build w suffix reg
  rw [withPublicChecks_ledger pre bus declaration_registered (by decide), declaration_lanes pre]
  have perLane (d : Bool) (i : Fin 8) : (hintHostTable pre (declarationLane d i)).interactionsWith bus =
      (WriteMixedHostTables.table run.1 data (.bank d (some i))).interactionsWith bus := by
    let id := WriteMixedHostTables.Index.bank d (some i)
    have cells := Option.some.inj ((built_hint_host_rows w suffix reg (declarationLane d i)).symm.trans
      (WriteMixedHostTables.original_arrays run routed data hint header remaining packets id))
    apply Table.interactionsWith_eq_of_rows _ _ _ cells
    apply congrArg (fun c : Component F => c.operations.interactionsWith bus)
    rw [hintHostTable_component, WriteMixedHostTables.registered]
    cases d <;> fin_cases i <;> rfl
  exact congrArg₂ List.append (List.flatMap_congr (fun i _ => perLane false i))
    (List.flatMap_congr (fun i _ => perLane true i))

end SP1Clean.Export.WriteObservationAssembly
