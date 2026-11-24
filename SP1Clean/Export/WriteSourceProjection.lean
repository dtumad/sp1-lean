import SP1Clean.Export.WriteSourceInstallation
import ToClean.Air.EnsembleRelabel

/-! # Projecting the supervisor's native WRITE publications onto original physical rows -/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

private abbrev retained (ch : RawChannel F) := ch ≠ readbackChannel.toRaw

private abbrev Layout := Component.SameRows retained

private theorem ordinary_layout (id : InstructionChipId) :
    Layout (ProtectedOrdinaryReceipt.component id) (OrdinarySources.component id) := by
  refine ⟨(publisher_name (.ordinary id)).symm, (OrdinarySources.width id).symm, ?_,
    (OrdinarySources.constraints id).symm, (OrdinarySources.lookups id).symm,
    fun ch other => (OrdinarySources.interactions id ch other).symm⟩
  funext rows
  dsimp only [OrdinarySources.component, ProtectedOrdinaryReceipt.component, Component.FixedRowsMatch]
  split <;> rfl

private theorem host_layout (family : HostSources.Family) :
    Layout (HostSources.original family) (HostSources.component family) := by
  refine ⟨(publisher_name (.host family)).symm, (Receipt.many_width _ _ (fun _ _ => trivial) _).symm, ?_,
    (Receipt.many_constraints _ _ (fun _ _ => trivial) _).symm,
    (Receipt.many_lookups _ _ (fun _ _ => trivial) _).symm,
    fun ch other => (Receipt.many_interactions _ _ (fun _ _ => trivial) _ ch other).symm⟩
  cases family with
  | ecall => rfl
  | word last => cases last <;> rfl

private theorem refresh_layout : Layout (original .refresh) refreshComponent := by
  refine ⟨(publisher_name .refresh).symm, (Receipt.width _ _ (fun _ _ => trivial) _).symm, rfl,
    (Receipt.constraints _ _ (fun _ _ => trivial) _).symm,
    (Receipt.lookups _ _ (fun _ _ => trivial) _).symm, fun ch other => (refresh_original_interactions ch other).symm⟩

private theorem final_layout (ram : Bool) : Layout (originalFinal ram) (finalComponent ram) := by
  refine ⟨(publisher_name (.finalizer ram)).symm, rfl, (final_fixed ram).symm,
    (Receipt.constraints _ _ (fun _ _ => trivial) _).symm,
    (Receipt.lookups _ _ (fun _ _ => trivial) _).symm, fun ch other => (final_original_interactions ram ch other).symm⟩

private theorem publisher_layout (id : Source) : Layout (original id) (publisher id) := by
  cases id with
  | ordinary id => exact ordinary_layout id
  | host family => exact host_layout family
  | refresh => exact refresh_layout
  | finalizer ram => exact final_layout ram

attribute [local irreducible] base withSources

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

private abbrev old := base image source target final
private abbrev extended := withSources image source target final

private theorem layout_at (index : Fin (old image source target final).tables.length) :
    Layout (old image source target final).tables[index.val]
      (decorate index.val (old image source target final).tables[index.val]) := by
  unfold decorate
  cases found : sourceAt index.val with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | some id =>
    have same := original_at image source target final id
    have pos : position id = index.val := eq_of_beq (List.find?_some (p := fun x => position x == index.val) found)
    rw [pos, List.getElem?_eq_getElem index.isLt, Option.some.injEq] at same
    rw [same]
    exact publisher_layout id

private theorem size_eq : (extended image source target final).tables.length = (old image source target final).tables.length := by
  rw [tables_eq, List.length_mapIdx]

private theorem placement (index : Fin (old image source target final).tables.length) :
    Layout (old image source target final).tables[index.val]
      ((extended image source target final).tables[index.val]'(by rw [size_eq]; exact index.isLt)) := by
  simp only [extended, tables_eq, List.getElem_mapIdx]
  exact layout_at image source target final index

/-- Read-back publication is a two-way relabeling on every other physical channel. -/
theorem sameRows : Ensemble.SameRows retained (old image source target final) (extended image source target final) :=
  Ensemble.SameRows.ofDecoration retained (base image source target final) (withSources image source target final)
    (size_eq image source target final) (verifier_eq image source target final) (placement image source target final)

variable {image source target final}

/-- Erase the additional publications, retaining all supervisor rows, headers and data. -/
def project (witness : EnsembleWitness (extended image source target final)) : EnsembleWitness (old image source target final) :=
  (sameRows ..).transport witness

theorem project_data (witness : EnsembleWitness (extended image source target final)) :
    (project witness).data = witness.data := (sameRows ..).data witness

theorem project_constraints (witness : EnsembleWitness (extended image source target final))
    (checked : witness.Constraints) : (project witness).Constraints := (sameRows ..).constraints witness checked

/-- The projection preserves each original signed ledger, including repeated and inactive occurrences. -/
theorem project_ledger (witness : EnsembleWitness (extended image source target final))
    (channel : RawChannel F) (other : channel ≠ readbackChannel.toRaw) :
    (project witness).interactionsWith channel = witness.interactionsWith channel :=
  (sameRows ..).ledger witness channel other

/-- Decorate an arbitrary original witness, reusing each original physical row and the header. -/
def installSources (witness : EnsembleWitness (old image source target final)) : EnsembleWitness (extended image source target final) :=
  (sameRows ..).symm.transport witness

theorem installSources_data (witness : EnsembleWitness (old image source target final)) :
    (installSources witness).data = witness.data := (sameRows ..).symm.data witness

theorem installSources_constraints (witness : EnsembleWitness (old image source target final))
    (checked : witness.Constraints) : (installSources witness).Constraints := (sameRows ..).symm.constraints witness checked

theorem installSources_ledger (witness : EnsembleWitness (old image source target final))
    (channel : RawChannel F) (other : channel ≠ readbackChannel.toRaw) :
    (installSources witness).interactionsWith channel = witness.interactionsWith channel :=
  (sameRows ..).symm.ledger witness channel other

variable (image source target final)

/-- Position of a genuine old source, selected by the complete physical component identity. -/
def originalSlot (id : Source) : TableSlot (old image source target final).tables (original id) :=
  TableSlot.ofGetElem? (original_at image source target final id)

/-- The installed publisher occupies the very same slot as its original source. -/
def publisherSlot (id : Source) : TableSlot (extended image source target final).tables (publisher id) :=
  TableSlot.ofGetElem? (publisher_at image source target final id)

@[simp] theorem originalSlot_index (id : Source) :
    (originalSlot image source target final id).index.val = position id :=
  TableSlot.ofGetElem?_index (original_at image source target final id)

@[simp] theorem publisherSlot_index (id : Source) :
    (publisherSlot image source target final id).index.val = position id :=
  TableSlot.ofGetElem?_index (publisher_at image source target final id)

private theorem slots_position (id : Source) :
    (originalSlot image source target final id).index.val = (publisherSlot image source target final id).index.val :=
  (originalSlot_index image source target final id).trans (publisherSlot_index image source target final id).symm

variable {image source target final}

/-- Physical sources with their genuine canonical data, selected before read-back decoration. -/
def raw (w : EnsembleWitness (base image source target final)) (id : Source) : Table F :=
  (originalSlot image source target final id).table w

theorem raw_registered (w : EnsembleWitness (base image source target final)) (id : Source) :
    (raw w id).component = original id := (originalSlot image source target final id).table_component w

private theorem published_fields (id : Source) (t : Table F) (component : t.component = original id) :
    let extended := publish id t component
    extended.component = publisher id ∧ extended.table = t.table ∧ extended.data = t.data := by
  cases id <;> exact ⟨rfl, rfl, rfl⟩

/-- Reattaching the receipt to an original projected table recovers the literal installed table,
including the committed data used by its physical environments. -/
theorem publish_project (w : EnsembleWitness (extended image source target final)) (id : Source) :
    let oldSlot := originalSlot image source target final id
    publish id (oldSlot.table (project w)) (oldSlot.table_component _) =
      (publisherSlot image source target final id).table w :=
  by
    dsimp only
    let src := originalSlot image source target final id
    let dest := publisherSlot image source target final id
    let raw := src.table (project w)
    have registered : raw.component = original id := src.table_component (project w)
    have fields := published_fields id raw registered
    apply (sameRows image source target final).reattach src dest (slots_position image source target final id) w (publish id raw registered)
    exact fields

/-- Honest generation can also publish directly from every original physical source in its slot. -/
theorem installSources_publish (w : EnsembleWitness (old image source target final)) (id : Source) :
    let oldSlot := originalSlot image source target final id
    (publisherSlot image source target final id).table (installSources w) =
      publish id (oldSlot.table w) (oldSlot.table_component _) :=
  by
    dsimp only
    let src := originalSlot image source target final id
    let dest := publisherSlot image source target final id
    let raw := src.table w
    have registered : raw.component = original id := src.table_component w
    have fields := published_fields id raw registered
    apply (sameRows image source target final).symm.attach dest src (slots_position image source target final id).symm w (publish id raw registered)
    exact fields

end SP1Clean.Export.WriteSourceRegistry
