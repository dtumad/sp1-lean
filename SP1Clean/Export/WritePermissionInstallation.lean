import SP1Clean.Export.WriteMixedPermissionLedger
import ToClean.Air.TableEvaluation

/-! # The original permission guard and all six consumers after physical installation -/

namespace SP1Clean.Export.WriteMixedPermissionLedger

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WritePermissionProvider
open WriteSourceRegistry WriteMixedSourceTables
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
    {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedFixedResources.Remaining image source target finish)

/-- The verifier-selected original guard occupies position 61. -/
def guardSlot (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F) :
    TableSlot (base image source target finish).tables (WritePermissionProvider.component image) :=
  TableSlot.ofGetElem? (WriteMixedFixedResources.registered_at image source target finish (.permission false))

attribute [local irreducible] base ofExecution compiledSource WriteMixedFixedResources.install WriteMixedHostTables.install

/-- The guard and the complete STORE and HINT_READ families fund one another at their
actual positions in the original supervisor, including every disabled row. -/
theorem installed_clients :
    let host := WriteMixedFixedResources.install run routed data hint packets remaining
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    LogUpBalanced (((guardSlot image source target finish).table w).interactionsWith channel.toRaw ++
      stores.flatMap (fun id => (raw w (.ordinary id)).interactionsWith channel.toRaw) ++
      (raw w (.host (.word false))).interactionsWith channel.toRaw ++ (raw w (.host (.word true))).interactionsWith channel.toRaw) := by
  intro host w
  let slot := guardSlot image source target finish
  let prior := WriteMixedHostTables.install run.1 data host
  let sources := compiledSource run routed data hint packets
  have eqSource (id : WriteProbe.AccessInventory.Source) : (raw w id).interactionsWith channel.toRaw = (sources id).interactionsWith channel.toRaw :=
    Table.interactionsWith_eq_of_rows _ _ _ (compiledSource_rows run routed data hint packets finish header prior id)
      (congrArg (fun c : Component F => c.operations.interactionsWith channel.toRaw) ((raw_registered w id).trans (compiledSource_registered run routed data hint packets id).symm))
  have cell := WriteMixedFixedResources.original_arrays run routed data hint packets header remaining (.permission false)
  have inside : slot.index.val < w.tables.length := w.same_length ▸ slot.index.isLt
  change (w.tables.map Table.table)[slot.index.val]? = some _ at cell
  rw [List.getElem?_map,List.getElem?_eq_getElem inside,Option.map_some] at cell
  have guard := Table.interactionsWith_eq_of_rows (slot.table w) (MixedPermissionDemand.guardTable run.1 routed data) channel.toRaw
    (Option.some.inj cell) (congrArg (fun c : Component F => c.operations.interactionsWith channel.toRaw) (slot.table_component w))
  change LogUpBalanced ((slot.table w).interactionsWith _ ++ _ ++ _ ++ _)
  simp only [guard,eqSource]
  exact generated run routed data hint packets

end SP1Clean.Export.WriteMixedPermissionLedger
