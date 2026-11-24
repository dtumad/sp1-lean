import SP1Clean.Export.WriteMixedHostAssembly
import SP1Clean.Export.WriteOriginalInstallation

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

/-- A generated provider occupies its original position at the full witness's shared data.
Its committed cells and all signed channel occurrences are exactly the generator's. -/
def InstalledAt (full : EnsembleWitness (WriteObservationAssembly.preprocessing image source target finish))
    (id : Index) (original : Table F) : Prop :=
  ∃ actual, full.tables[position id]? = some actual ∧ actual.component = component id ∧ actual.table = original.table ∧
    actual.data = full.data ∧ actual.Constraints ∧ actual.Guarantees ∧
    ∀ ch, actual.interactionsWith ch = original.interactionsWith ch

/-- Each of the 22 generated original tables is checked at its actual slot and canonical
prover data in the native observer. Every original signed occurrence has the same payload,
multiplicity and order, independently of all other generators' validity. -/
theorem installed_at (suffix : List (Table F)) (registeredSuffix : suffix.map Table.component = WriteObservationAssembly.tables source target)
    (id : Index) :
    let original := table run.1 data id
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (install run.1 data remaining) packets
    let full := WriteObservationAssembly.build w suffix registeredSuffix
    InstalledAt full id original := by
  intro original w full
  have reg := registered run.1 data id
  have old := registered_at image source target finish id
  have atSlot : (base image source target finish).tables[position id]? = some original.component := old.trans (congrArg some reg.symm)
  obtain ⟨actual,located,comp,cells,shared⟩ := WriteObservationAssembly.build_original_cells w suffix registeredSuffix atSlot (outside_memory id)
    (original_arrays run routed data hint header remaining packets id)
  have free := HostObserved.lookupFree (image := image) (source := source) (target := target) (final := finish) original.component (List.mem_of_getElem? atSlot)
  exact ⟨actual,located,comp.trans reg,cells,shared,WriteObservationAssembly.checks_of_original_cells comp cells (valid run.1 data id) free
    (fun i member => channel_transfer id i (reg ▸ member))⟩

end SP1Clean.Export.WriteMixedHostTables
