import SP1Clean.Export.WritePermissionSupport

/-! # Every original supervisor occurrence on the write-permission channel -/

namespace SP1Clean.Export.WriteMixedPermissionLedger
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WritePermissionProvider WriteSourceRegistry WriteProbe.AccessInventory
open WriteMixedSourceTables
private abbrev F := ZMod SP1Prime
private abbrev bus := (channel (p := SP1Prime)).toRaw
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
attribute [local irreducible] base ofExecution

private noncomputable def physical (w : EnsembleWitness (base image source target finish)) (i : ℕ) :=
  w.tables[i]?.toList.flatMap (·.interactionsWith bus)

private theorem physical_at {component : Component F} (w : EnsembleWitness (base image source target finish))
    (slot : TableSlot (base image source target finish).tables component) :
    physical w slot.index.val = (slot.table w).interactionsWith bus := by
  have inside : slot.index.val < w.tables.length := w.same_length ▸ slot.index.isLt
  simp only [physical,List.getElem?_eq_getElem inside,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

private theorem slot_order (n : ℕ) (size : n = 98) :
    (List.finRange n).filterMap (fun i => if i.val ∈ permissionPositions then some i.val else none) = permissionPositions := by
  subst n; decide

private theorem physical_ledger (w : EnsembleWitness (base image source target finish)) :
    w.interactionsWith bus = permissionPositions.flatMap (physical w) := by
  change w.verifierInteractionsWith bus ++ w.tables.flatMap (·.interactionsWith bus) = _
  rw [verifier_silent,List.nil_append]
  have size := w.same_length.symm.trans (base_length image source target finish)
  conv_rhs => rw [← slot_order w.tables.length size,List.filterMap_eq_flatMap_toList,List.flatMap_assoc]
  conv_lhs => rw [← List.ofFn_getElem (xs := w.tables),List.ofFn_eq_map,List.flatMap_map]
  apply List.flatMap_congr; intro i _
  by_cases selected : i.val ∈ permissionPositions
  · simp only [selected,↓reduceIte,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,physical,List.getElem?_eq_getElem i.isLt]
  · simp only [selected,↓reduceIte,Option.toList_none,List.flatMap_nil]
    apply Table.interactionsWith_nil_of_channel_not_mem
    have inBase : i.val < (base image source target finish).tables.length := by rw [w.same_length]; exact i.isLt
    apply table_silent (i := i.val) (image := image) (source := source) (target := target) (finish := finish) _ selected
    rw [List.getElem?_eq_getElem inBase,← w.same_circuits i.val inBase]

/-- The complete original permission ledger in physical order for an arbitrary witness. -/
theorem supervisor_ledger (w : EnsembleWitness (base image source target finish)) :
    w.interactionsWith bus = stores.flatMap (fun id => (raw w (.ordinary id)).interactionsWith bus) ++
      ((guardSlot image source target finish).table w).interactionsWith bus ++
      (raw w (.host (.word false))).interactionsWith bus ++ (raw w (.host (.word true))).interactionsWith bus := by
  have fromSource (id : Source) : physical w (position id) = (raw w id).interactionsWith bus :=
    physical_at w (originalSlot image source target finish id)
  have guard : physical w 61 = ((guardSlot image source target finish).table w).interactionsWith bus :=
    physical_at w (guardSlot image source target finish)
  rw [physical_ledger]
  simp only [permissionPositions,stores,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [← fromSource (.ordinary .storeByte),← fromSource (.ordinary .storeHalf),← fromSource (.ordinary .storeWord),← fromSource (.ordinary .storeDouble),
    ← guard,← fromSource (.host (.word false)),← fromSource (.host (.word true))]
  rfl

/-- The complete byte-permission ledger balances on the constructed original supervisor. -/
theorem supervisor_balanced {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedFixedResources.Remaining image source target finish) :
    let host := WriteMixedFixedResources.install run routed data hint packets remaining
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    LogUpBalanced (w.interactionsWith bus) := by
  intro host w msg
  have paid := installed_clients run routed data hint packets header remaining msg
  rw [supervisor_ledger]
  simp only [balanceOf_append] at paid ⊢
  rwa [add_comm (balanceOf (stores.flatMap _) msg)]

end SP1Clean.Export.WriteMixedPermissionLedger
