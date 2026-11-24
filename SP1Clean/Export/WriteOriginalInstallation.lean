import SP1Clean.Export.WriteObservationBuild

/-! # Original physical tables retained by the native observation assembly -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteSourceRegistry
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- At each original slot outside the Memory receipt registry, installation retains the
generated cells and their original component under the complete witness's canonical data. -/
theorem build_original_cells (w : EnsembleWitness (base image source target finish)) (suffix : List (Table F))
    (registered : suffix.map Table.component = tables source target) {i : ℕ} {original : Table F}
    (atSlot : (base image source target finish).tables[i]? = some original.component)
    (outside : sourceAt i = none) (generated : (w.tables.map Table.table)[i]? = some original.table) :
    let full := build w suffix registered
    ∃ actual, full.tables[i]? = some actual ∧ actual.component = original.component ∧ actual.table = original.table ∧ actual.data = full.data := by
  intro full
  have inOriginal := (List.getElem?_eq_some_iff.mp atSlot).1
  have inside : i < (withSources image source target finish).tables.length := by rwa [← (sameRows image source target finish).length]
  have whereAt : (preprocessing image source target finish).tables[i]? = some original.component := by
    rw [(appended image source target finish).tables,List.getElem?_append_left inside,tables_eq,List.getElem?_mapIdx,atSlot]
    simp only [Option.map_some,decorate,outside,Option.elim_none]
  let actual := full.tables[i]'(by rw [← full.same_length]; exact (List.getElem?_eq_some_iff.mp whereAt).1)
  have located : full.tables[i]? = some actual := List.getElem?_eq_getElem _
  have comp := congrArg (fun cs : List (Component F) => cs[i]?) full.tables_map_component
  simp only [List.getElem?_map,located,Option.map_some,whereAt] at comp
  have arrays : full.tables.map Table.table = ((installSources w).tables ++ suffix).map Table.table := by
    dsimp only [full,build,Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables,withDerivedData_map_table]
  have cells := congrArg (fun rs : List (List (Array F)) => rs[i]?) arrays
  simp only [List.getElem?_map,located,Option.map_some] at cells
  rw [List.getElem?_append_left (by rw [← (installSources w).same_length]; exact inside),
    List.getElem?_eq_getElem (by rw [← (installSources w).same_length]; exact inside),Option.map_some] at cells
  rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [← w.same_length]; exact inOriginal),Option.map_some] at generated
  exact ⟨actual,located,Option.some.inj comp,(Option.some.inj cells).trans (((sameRows image source target finish).symm.rows w ⟨i,inside⟩).trans
    (Option.some.inj generated)),full.same_data _ (List.mem_of_getElem? located)⟩

/-- Local checks and every signed occurrence survive canonical data replacement on an
unchanged, lookup-free component whose channel guarantees are independent of prover data. -/
theorem checks_of_original_cells {actual original : Table F}
    (same : actual.component = original.component) (cells : actual.table = original.table)
    (checked : original.Constraints ∧ original.Guarantees) (free : original.component.operations.lookups = [])
    (transfer : ∀ (i : Interaction F), i.channel ∈ original.component.circuit.channels → i.Guarantees original.data → i.Guarantees actual.data) :
    actual.Constraints ∧ actual.Guarantees ∧ ∀ ch, actual.interactionsWith ch = original.interactionsWith ch := by
  have interactions : actual.interactions = original.interactions := by
    simp only [Table.interactions,Table.environment,same,cells]
    apply List.flatMap_congr
    exact fun _ _ => Operations.interactionValues_congr rfl
  refine ⟨?_,actual.guarantees_iff_forall.mpr ?_,?_⟩
  · intro row present
    have valid := original.component.constraintsHold_setData (data' := actual.data) free (checked.1 row (cells ▸ present))
    change actual.component.operations.ConstraintsHold (Environment.fromArray row actual.data)
    rwa [same]
  · intro i present
    exact transfer i (same ▸ actual.channel_mem_channels_of_mem_interactions i present)
      (original.guarantees_iff_forall.mp checked.2 i (interactions ▸ present))
  · intro ch
    rw [Table.interactionsWith_eq_filter,Table.interactionsWith_eq_filter,interactions]

/-- An original channel whose name is absent from every observer component and both public
endpoints retains its exact original ledger, including its public boundary occurrences. -/
theorem public_original_ledger (w : EnsembleWitness (base image source target finish)) (suffix : List (Table F))
    (registered : suffix.map Table.component = tables source target) (ch : RawChannel F)
    (original : ch ∈ (base image source target finish).channels)
    (outside : ch ≠ WriteProbe.readbackChannel.toRaw)
    (silent : ch.name ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name))
    (endpoints : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name]) :
    (withPublicChecks (build w suffix registered)).interactionsWith ch = w.interactionsWith ch := by
  have full : ch ∈ (preprocessing image source target finish).channels := by
    unfold preprocessing
    change _ ∈ channels ++ (withSources image source target finish).channels
    rw [channels_eq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ original)
  have empty : suffix.flatMap (·.interactionsWith ch) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t used
    apply Table.interactionsWith_nil_of_channel_not_mem
    exact fun member => silent (List.mem_flatMap.mpr ⟨t.component,registered ▸ List.mem_map_of_mem used,List.mem_map_of_mem member⟩)
  rw [withPublicChecks_ledger _ _ full endpoints,build_ledger,empty,List.append_nil,installSources_ledger _ _ outside]

end SP1Clean.Export.WriteObservationAssembly
