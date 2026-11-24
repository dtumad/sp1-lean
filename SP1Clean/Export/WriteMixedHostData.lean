import SP1Clean.Export.WriteMixedHostAssembly
import SP1Clean.Export.WriteObservationBuild

/-! # Authenticated bank and ordinary observation tables at the complete observer's data

At all 22 positions the physical row arrays and every signed ledger survive receipt installation
and canonicalization against the complete public header. Local checks at those positions therefore
do not require any facts about the residual generators.
-/

namespace SP1Clean.Export.WriteMixedHostTables

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WriteSourceRegistry

private abbrev F := ZMod SP1Prime

private theorem after_boundary (id : Index) : 6 ≤ position id := by
  cases id <;> simp only [position] <;> omega

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
    {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (remaining : Remaining image source target finish)
    (packets : List WriteObservations.Packet)

/-- The original precursor to the WRITE observer has the same generated cells at every protocol slot. -/
theorem original_arrays (id : Index) :
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (install run.1 data remaining) packets
    (w.tables.map Table.table)[position id]? = some (table run.1 data id).table := by
  intro w
  have inBase := (List.getElem?_eq_some_iff.mp (registered_at image source target finish id)).1
  have first := after_boundary id
  let i : Fin ((base image source target finish).tables.drop 6).length := ⟨position id - 6, by rw [List.length_drop]; omega⟩
  have offset : 6 + i.val = position id := by dsimp only [i]; omega
  have absent : sourceAt (6 + i.val) = none := offset ▸ outside_memory id
  have found : indexAt (6 + i.val) = some id := offset ▸ indexAt_position id
  have physical : (w.tables.map Table.table)[6 + i.val]? = some ((install run.1 data remaining i absent).1.table) :=
    WriteMixedSourceTables.remaining_arrays image source target finish rows (HintReadTransfers.history image source events)
      (WriteMixedSourceTables.heights run routed) data hint (install run.1 data remaining) _ _ _ header i absent
  rwa [install_at run.1 data remaining i absent found, offset] at physical

private theorem channel_transfer (id : Index) (i : Interaction F) (member : i.channel ∈ (component id).circuit.channels)
    {old fresh : ProverData F} (accepted : i.Guarantees old) : i.Guarantees fresh := by
  have every : ∀ ch ∈ (component id).circuit.channels, ∀ (item : Interaction F),
      item.channel = ch → item.Guarantees old → item.Guarantees fresh := by
    rcases id with ⟨d, idx⟩ | k
    all_goals first | cases idx <;> cases d | fin_cases k
    all_goals repeat' refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
    all_goals first
      | exact fun _ mem => False.elim (List.not_mem_nil mem)
      | intro ⟨ch, _, _, _, _⟩ same valid
        change ch = _ at same
        subst ch
        exact valid
  exact every _ member i rfl accepted

private theorem checks_of_cells {id : Index} {actual original : Table F}
    (actualComponent : actual.component = component id) (originalComponent : original.component = component id)
    (cells : actual.table = original.table) (checked : original.Constraints ∧ original.Guarantees)
    (free : (component id).operations.lookups = []) :
    actual.Constraints ∧ actual.Guarantees ∧ ∀ ch, actual.interactionsWith ch = original.interactionsWith ch := by
  have same := actualComponent.trans originalComponent.symm
  have interactions : actual.interactions = original.interactions := by
    simp only [Table.interactions, Table.environment, same, cells]
    apply List.flatMap_congr
    exact fun _ _ => Operations.interactionValues_congr rfl
  refine ⟨?_, actual.guarantees_iff_forall.mpr ?_, ?_⟩
  · intro row present
    have before := checked.1 row (cells ▸ present)
    rw [← originalComponent] at free
    have valid := original.component.constraintsHold_setData (data' := actual.data) free before
    change actual.component.operations.ConstraintsHold (Environment.fromArray row actual.data)
    rwa [same]
  · intro i present
    exact channel_transfer id i (actualComponent ▸ actual.channel_mem_channels_of_mem_interactions i present)
      (original.guarantees_iff_forall.mp checked.2 i (interactions ▸ present))
  · intro ch
    rw [Table.interactionsWith_eq_filter, Table.interactionsWith_eq_filter, interactions]

private theorem full_components (id : Index) :
    (WriteObservationAssembly.preprocessing image source target finish).tables[position id]? = some (component id) := by
  let appended := WriteObservationAssembly.appended image source target finish
  have before := registered_at image source target finish id
  have inside := (List.getElem?_eq_some_iff.mp before).1
  rw [appended.tables, List.getElem?_append_left (by rw [← (sameRows image source target finish).length]; exact inside),
    tables_eq, List.getElem?_mapIdx, before]
  simp only [Option.map_some, decorate, outside_memory, Option.elim_none]

/-- A generated provider occupies its original position at the full witness's shared data.
Its committed cells and all signed channel occurrences are exactly the generator's. -/
def InstalledAt (full : EnsembleWitness (WriteObservationAssembly.preprocessing image source target finish))
    (id : Index) (original : Table F) : Prop :=
  ∃ actual, full.tables[position id]? = some actual ∧ actual.component = component id ∧ actual.table = original.table ∧
    actual.data = full.data ∧ actual.Constraints ∧ actual.Guarantees ∧
    ∀ ch, actual.interactionsWith ch = original.interactionsWith ch

/-- Each of the 22 generated original tables is checked at its actual slot and canonical
prover data in the 113-table observer. Every original signed occurrence has the same payload,
multiplicity and order, independently of all other generators' validity. -/
theorem installed_at (suffix : List (Table F)) (registeredSuffix : suffix.map Table.component = WriteObservationAssembly.tables source target)
    (id : Index) :
    let original := table run.1 data id
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (install run.1 data remaining) packets
    let full := WriteObservationAssembly.build w suffix registeredSuffix
    InstalledAt full id original := by
  intro original w full
  have whereAt := full_components (image := image) (source := source) (target := target) (finish := finish) id
  have inside := (List.getElem?_eq_some_iff.mp whereAt).1
  have old := registered_at image source target finish id
  have inOriginal := (List.getElem?_eq_some_iff.mp old).1
  have inReceipt : position id < (withSources image source target finish).tables.length := by rwa [← (sameRows image source target finish).length]
  let actual := full.tables[position id]'(by rw [← full.same_length]; exact inside)
  have located : full.tables[position id]? = some actual := List.getElem?_eq_getElem _
  have own := congrArg (fun cs : List (Component F) => cs[position id]?) full.tables_map_component
  simp only [List.getElem?_map, located, Option.map_some, whereAt] at own
  have componentEq := Option.some.inj own
  have arrays : full.tables.map Table.table = ((installSources w).tables ++ suffix).map Table.table := by
    dsimp only [full, WriteObservationAssembly.build, Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables, withDerivedData_map_table]
  have sameRow := (sameRows image source target finish).symm.rows w ⟨position id, inReceipt⟩
  have previous := original_arrays run routed data hint header remaining packets id
  change (w.tables.map Table.table)[position id]? = some original.table at previous
  rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [← w.same_length]; exact inOriginal)] at previous
  have cells := congrArg (fun rs : List (List (Array F)) => rs[position id]?) arrays
  simp only [List.getElem?_map, located, Option.map_some] at cells
  rw [List.getElem?_append_left (by rw [← (installSources w).same_length]; exact inReceipt),
    List.getElem?_eq_getElem (by rw [← (installSources w).same_length]; exact inReceipt), Option.map_some] at cells
  have exactRows : actual.table = original.table := (Option.some.inj cells).trans (sameRow.trans (Option.some.inj previous))
  have free := HostObserved.lookupFree (image := image) (source := source) (target := target) (final := finish)
    (component id) (List.mem_of_getElem? old)
  exact ⟨actual, located, componentEq, exactRows, full.same_data _ (List.mem_of_getElem? located), checks_of_cells componentEq (registered run.1 data id) exactRows (valid run.1 data id) free⟩

end SP1Clean.Export.WriteMixedHostTables
