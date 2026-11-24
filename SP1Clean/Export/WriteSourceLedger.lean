import SP1Clean.Export.WriteSourceProjection

/-! # The complete read-back ledger at the installed supervisor registry -/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

attribute [local irreducible] base withSources

private theorem readback_absent : readbackChannel.toRaw ∉ (base image source target final).channels := by
  have names := (withSources image source target final).unique_channel_names
  rw [channels_eq, List.map_cons, List.nodup_cons] at names
  exact fun used => names.1 (List.mem_map_of_mem (f := RawChannel.name) used)

private theorem verifier_silent (env : Environment F) :
    (withSources image source target final).verifierOperations.interactionValuesWith readbackChannel.toRaw env = [] := by
  change ((withSources image source target final).verifier.operations.circuitOperations).interactionValuesWith _ env = []
  rw [verifier_eq]
  have empty : (base image source target final).verifierOperations.interactionsWith readbackChannel.toRaw = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro interaction member
    change interaction ∈ (base image source target final).verifier.operations.circuitOperations.interactions at member
    rw [Verifier.Operations.circuitOperations_interactions] at member
    have registered := (base image source target final).verifier_channels
      (Verifier.Operations.channel_mem_of_mem_interactions member)
    have ne : interaction.channel ≠ readbackChannel.toRaw :=
      fun equal => readback_absent image source target final (equal ▸ registered)
    simpa using ne
  exact congrArg (List.map (AbstractInteraction.eval env)) empty

variable {image source target final}

/-- The original source tables, with all their rows and canonical supervisor data. -/
def rawSource (w : EnsembleWitness (withSources image source target final)) (id : Source) : Table F :=
  (originalSlot image source target final id).table (project w)

theorem rawSource_component (w : EnsembleWitness (withSources image source target final)) (id : Source) :
    (rawSource w id).component = original id := (originalSlot image source target final id).table_component _

private theorem ordinary_at {i : ℕ} (found : sourceAt i = none)
    (installed : i < (withSources image source target final).tables.length)
    (prior : i < (base image source target final).tables.length) :
    (withSources image source target final).tables[i] = (base image source target final).tables[i] := by
  simp only [tables_eq, List.getElem_mapIdx, decorate, found, Option.elim_none]

private theorem table_ledger_at (w : EnsembleWitness (withSources image source target final)) (i : Fin w.tables.length) :
    w.tables[i.val].interactionsWith readbackChannel.toRaw = (sourceAt i.val).toList.flatMap
      (fun id => (publish id (rawSource w id) (rawSource_component w id)).interactionsWith readbackChannel.toRaw) := by
  cases found : sourceAt i.val with
  | some id =>
    have pos : position id = i.val := eq_of_beq (List.find?_some (p := fun s => position s == i.val) found)
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, rawSource, publish_project]
    unfold TableSlot.table
    apply congrArg (fun t : Table F => t.interactionsWith readbackChannel.toRaw)
    exact getElem_congr_idx (pos.symm.trans (publisherSlot_index image source target final id).symm)
  | none =>
    change w.tables[i.val].interactionsWith readbackChannel.toRaw = []
    apply Table.interactionsWith_nil_of_channel_not_mem
    intro used
    have inNew : i.val < (withSources image source target final).tables.length := by rw [w.same_length]; exact i.isLt
    have same := w.same_circuits i.val inNew
    have inOld : i.val < (base image source target final).tables.length := by
      simpa only [tables_eq, List.length_mapIdx] using inNew
    have original := same.symm.trans (ordinary_at found inNew inOld)
    exact readback_absent image source target final ((base image source target final).tables_channels _
      (List.getElem_mem inOld) (original ▸ used))

private theorem indexOrder (n : ℕ) (size : n = 98) :
    ((List.finRange n).filterMap (fun i => sourceAt i.val)).Perm sources := by
  subst n
  decide

/-- The added protocol on the decorated registry contains exactly the 31 true source ledgers.
The permutation changes component-group order only; every signed padding occurrence remains. -/
theorem readback_ledger (w : EnsembleWitness (withSources image source target final)) :
    (w.interactionsWith readbackChannel.toRaw).Perm
      (sources.flatMap (fun id =>
        (publish id (rawSource w id) (rawSource_component w id)).interactionsWith readbackChannel.toRaw)) := by
  let f := fun id => (publish id (rawSource w id) (rawSource_component w id)).interactionsWith readbackChannel.toRaw
  change (_ ++ w.tables.flatMap (·.interactionsWith readbackChannel.toRaw)).Perm (sources.flatMap f)
  rw [show w.verifierInteractionsWith readbackChannel.toRaw = [] from verifier_silent image source target final _, List.nil_append]
  have size : w.tables.length = 98 := by rw [← w.same_length, tables_eq, List.length_mapIdx, base_length]
  have ordered := (indexOrder w.tables.length size).flatMap (f := f) (g := f) (fun _ _ => List.Perm.refl _)
  refine (List.Perm.of_eq ?_).trans ordered
  rw [List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
  conv_lhs => rw [← List.ofFn_getElem (xs := w.tables), List.ofFn_eq_map, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => table_ledger_at w i)

end SP1Clean.Export.WriteSourceRegistry
