import SP1Clean.Export.WriteSourceInstallation

/-! # Projecting the supervisor's native WRITE publications onto original physical rows -/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

/-- Data needed to erase a read-back publication while retaining everything the
original physical protocol can observe. -/
structure Layout (old new : Component F) : Prop where
  name : old.circuit.name = new.circuit.name
  width : old.width = new.width
  fixed : old.FixedRowsMatch = new.FixedRowsMatch
  constraints : old.operations.constraints = new.operations.constraints
  lookups : old.operations.lookups = new.operations.lookups
  interactions : ∀ channel, channel ≠ readbackChannel.toRaw →
    old.operations.interactionsWith channel = new.operations.interactionsWith channel

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

variable {image source target final}

/-- Erase the additional native publications and retain all original supervisor rows.
The original State and Memory balances can be transported independently of HostCall. -/
def project (witness : EnsembleWitness (extended image source target final)) : EnsembleWitness (old image source target final) :=
  witness.projectPrefix _ (size_eq ..).ge (fun i => (placement _ _ _ _ i).width.le) (fun i => (placement _ _ _ _ i).fixed)

theorem project_data (witness : EnsembleWitness (extended image source target final)) :
    (project witness).data = witness.data :=
  witness.projectPrefix_data_eq_of_layout _ _ _ (fun i => (placement _ _ _ _ i).width)
    (fun i => (placement _ _ _ _ i).name) (size_eq ..).symm

theorem project_constraints (witness : EnsembleWitness (extended image source target final))
    (checked : witness.Constraints) : (project witness).Constraints := by
  apply witness.projectPrefix_constraints_of _ _ _ _ checked
  intro i row size holds
  have entry := placement image source target final i
  have clip : row.extract 0 (old image source target final).tables[i.val].width = row := by
    rw [entry.width, ← size, Array.extract_size]
  change (old image source target final).tables[i.val].operations.ConstraintsHold
    (Environment.fromArray (row.extract 0 _) (project witness).data)
  simpa only [clip, project_data, Operations.ConstraintsHold, entry.constraints, entry.lookups] using holds

/-- For any original protocol the projection preserves every signed occurrence, in order.
This also transports zero multiplicities and repeated messages. -/
theorem project_ledger (witness : EnsembleWitness (extended image source target final))
    (channel : RawChannel F) (other : channel ≠ readbackChannel.toRaw) :
    (project witness).interactionsWith channel = witness.interactionsWith channel := by
  apply witness.projectPrefix_interactions _ _ _ (verifier_eq ..).symm channel
  · intro i row size
    have entry := placement image source target final i
    have clip : row.extract 0 (old image source target final).tables[i.val].width = row := by
      rw [entry.width, ← size, Array.extract_size]
    change (old image source target final).tables[i.val].operations.interactionValuesWith channel
      (Environment.fromArray (row.extract 0 _) (project witness).data) = _
    simp only [clip, project_data, Operations.interactionValuesWith, entry.interactions channel other]
  · rw [← size_eq, witness.same_length, List.drop_length]
    simp

end SP1Clean.Export.WriteSourceRegistry
