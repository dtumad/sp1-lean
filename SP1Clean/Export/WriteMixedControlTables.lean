import SP1Clean.Export.WriteMixedFixedResources
import SP1Clean.Export.WriteOriginalInstallation
import SP1Clean.Proofs.Completeness.MixedHaltPadding

/-! # Native CPU state normalizations and legacy Exit padding on a mixed execution -/

namespace SP1Clean.Export.WriteMixedControlTables
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry
private abbrev F := ZMod SP1Prime

/-- The two original control tables following the register refresh table. -/
inductive Index | stateBump | haltPadding deriving DecidableEq

/-- Position in the original physical registry. -/
def position : Index → Nat | .stateBump => 56 | .haltPadding => 57

/-- Recognize the physical control-table slots. -/
def indexAt (i : Nat) : Option Index := [.stateBump,.haltPadding].find? (fun k => position k == i)

/-- Actual components registered in the released-instruction supervisor. -/
def component : Index → Component F | .stateBump => providerTableFor .stateBump | .haltPadding => HaltPaddingChip.component

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

/-- Both native components are precisely registered at their stated position. -/
theorem registered_at (k : Index) : (base image source target finish).tables[position k]? = some (component k) := by
  cases k
  · exact stateBump_at image source target finish
  · exact halt_at image source target finish

private abbrev components := (base image source target finish).tables.drop 6

/-- The still-unconstructed original components after both control tables are installed. -/
def Remaining := (i : Fin (components image source target finish).length) →
  sourceAt (6 + i.val) = none → WriteMixedHostTables.indexAt (6 + i.val) = none → WriteMixedFixedResources.indexAt (6 + i.val) = none →
  indexAt (6 + i.val) = none → { t : Table F // t.component = (components image source target finish)[i] }

/-- Exactly 28 original slots remain for the lookup and host-handler compilers. -/
theorem remaining_count : ((List.range' 6 (components image source target finish).length).filter (fun i =>
    (sourceAt i).isNone && (WriteMixedHostTables.indexAt i).isNone && (WriteMixedFixedResources.indexAt i).isNone && (indexAt i).isNone)).length = 28 := by
  rw [List.length_drop,base_length]; decide

variable {image source target finish} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F)

/-- The state companion of the original mixed register refresh and the endpoint-selected
legacy Exit table. Both use the exact native row builders. -/
def table : Index → Table F
  | .stateBump => (InstalledAssembly.bumpTables (MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput))
      (MixedBumpInput.stateRows (rows.map MixedCompiledRow.bumpInput)) data (WriteMixedSourceTables.heights run routed).memory (WriteMixedSourceTables.heights run routed).state).2
  | .haltPadding => MixedHaltPadding.table source target data

/-- The two generated arrays have exactly their registered components. -/
theorem table_component (k : Index) : (table run routed data k).component = component k := by cases k <;> rfl

/-- Each generated normalization and checkpoint row satisfies its original physical circuit. -/
theorem table_valid (k : Index) : (table run routed data k).Constraints ∧ (table run routed data k).Guarantees := by
  cases k
  · obtain ⟨inputs,bumped,_,_,_,_,valid⟩ := admissibleExecution_mixedBumpInventory run.1
    rw [routeBumpInputs?,routed,Option.map_some] at bumped
    cases Option.some.inj bumped
    exact InstalledAssembly.bumpTables_stateValid _ _ data _ _ valid
  · have checked := MixedHaltPadding.checked source target data
    exact ⟨checked.1,checked.2.1⟩

/-- Physical height of the nonempty clock-window refresh bucket or its zero-demand shape,
and the complementary zero-or-one row for the public Exit receipt. -/
theorem heights : (table run routed data .stateBump).length = WitnessGeneration.demandHeight (MixedBumpInput.stateRows (rows.map MixedCompiledRow.bumpInput)).length ∧
    (table run routed data .haltPadding).length = (if (SP1StateBoundary.haltCode source target).isNone then 1 else 0) :=
  ⟨InstalledAssembly.bumpTables_stateLength _ _ data _ _,(MixedHaltPadding.checked source target data).2.2⟩

/-- Fill exactly slots 56 and 57, retaining the complementary callback for all earlier registries. -/
noncomputable def install (remaining : Remaining image source target finish) : WriteMixedFixedResources.Remaining image source target finish :=
  fun i absent host fixed => match found : indexAt (6 + i.val) with
    | none => remaining i absent host fixed found
    | some k => ⟨table run routed data k,by
        have atSlot := registered_at image source target finish k
        have pos : position k = 6 + i.val := eq_of_beq (List.find?_some (p := fun it => position it == 6 + i.val) found)
        rw [pos,← List.getElem?_drop,List.getElem?_eq_getElem i.isLt] at atSlot
        exact (table_component run routed data k).trans (Option.some.inj atSlot).symm⟩

/-- The two native constructors discharge their own local checks regardless of the remaining slots. -/
theorem install_valid (remaining : Remaining image source target finish)
    (checked : ∀ i a h f n, let t := (remaining i a h f n).1; t.Constraints ∧ t.Guarantees) :
    ∀ i a h f, let t := (install run routed data remaining i a h f).1; t.Constraints ∧ t.Guarantees := by
  intro i a h f
  dsimp only [install]
  split
  · exact checked i a h f _
  · exact table_valid run routed data _

variable (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : Remaining image source target finish)

/-- The real supervisor has exactly the generated normalization and padding row arrays. -/
theorem original_arrays (k : Index) :
    let fixed := install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    (w.tables.map Table.table)[position k]? = some (table run routed data k).table := by
  intro fixed host w
  have location : 6 ≤ position k ∧ sourceAt (position k) = none ∧ WriteMixedHostTables.indexAt (position k) = none ∧
      WriteMixedFixedResources.indexAt (position k) = none ∧ indexAt (position k) = some k := by cases k <;> decide
  have size := (List.getElem?_eq_some_iff.mp (registered_at image source target finish k)).1
  let i : Fin ((base image source target finish).tables.drop 6).length := ⟨position k - 6,by rw [List.length_drop]; omega⟩
  have offset : 6 + i.val = position k := by dsimp only [i]; omega
  have absent : sourceAt (6 + i.val) = none := offset ▸ location.2.1
  have old : WriteMixedHostTables.indexAt (6 + i.val) = none := offset ▸ location.2.2.1
  have other : WriteMixedFixedResources.indexAt (6 + i.val) = none := offset ▸ location.2.2.2.1
  have found : indexAt (6 + i.val) = some k := offset ▸ location.2.2.2.2
  have physical : (w.tables.map Table.table)[6 + i.val]? = some ((WriteMixedHostTables.install run.1 data host i absent).1.table) :=
    WriteMixedSourceTables.remaining_arrays image source target finish rows (HintReadTransfers.history image source events)
      (WriteMixedSourceTables.heights run routed) data hint (WriteMixedHostTables.install run.1 data host) _ _ _ header i absent
  have same : (WriteMixedHostTables.install run.1 data host i absent).1 = table run routed data k := by
    dsimp only [WriteMixedHostTables.install]; split
    · dsimp only [host,WriteMixedFixedResources.install]; split
      · dsimp only [fixed,install]; split
        · rename_i missing; exact False.elim (by rw [found] at missing; cases missing)
        · rename_i _ h
          cases Option.some.inj (h.symm.trans found)
          rfl
      · rename_i _ h; exact False.elim (by rw [other] at h; cases h)
    · rename_i _ h; exact False.elim (by rw [old] at h; cases h)
  rwa [same,offset] at physical

/-- A physical native control table after receipt installation and canonical data replacement. -/
def InstalledAt (full : EnsembleWitness (WriteObservationAssembly.preprocessing image source target finish)) (k : Index) (original : Table F) : Prop :=
  ∃ actual, full.tables[position k]? = some actual ∧ actual.component = component k ∧ actual.table = original.table ∧
    actual.data = full.data ∧ actual.Constraints ∧ actual.Guarantees ∧ ∀ ch, actual.interactionsWith ch = original.interactionsWith ch

private theorem transfer (k : Index) (i : Interaction F) (member : i.channel ∈ (component k).circuit.channels)
    {old fresh : ProverData F} (accepted : i.Guarantees old) : i.Guarantees fresh := by
  have every : ∀ ch ∈ (component k).circuit.channels, ∀ (item : Interaction F), item.channel = ch → item.Guarantees old → item.Guarantees fresh := by
    cases k
    all_goals repeat' refine List.forall_mem_cons.mpr ⟨?_,?_⟩
    all_goals first
      | exact fun _ mem => False.elim (List.not_mem_nil mem)
      | intro ⟨ch,_,_,_,_⟩ same valid; change ch = _ at same; subst ch; exact valid
  exact every _ member i rfl accepted

/-- Both control slots retain their generated traces, local assertions and complete physical
ledgers on the assembled witness, independently of the other original table generators. -/
theorem installed_at (suffix : List (Table F)) (registered : suffix.map Table.component = WriteObservationAssembly.tables source target) (k : Index) :
    let fixed := install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    InstalledAt (WriteObservationAssembly.build w suffix registered) k (table run routed data k) := by
  intro fixed host w
  let original := table run routed data k
  have reg : original.component = component k := table_component run routed data k
  have atSlot := (registered_at image source target finish k).trans (congrArg some reg.symm)
  have outside : sourceAt (position k) = none := by cases k <;> decide
  obtain ⟨actual,located,comp,cells,shared⟩ := WriteObservationAssembly.build_original_cells w suffix registered atSlot outside
    (original_arrays run routed data hint packets header remaining k)
  have free := HostObserved.lookupFree (image := image) (source := source) (target := target) (final := finish) original.component (List.mem_of_getElem? atSlot)
  exact ⟨actual,located,comp.trans reg,cells,shared,WriteObservationAssembly.checks_of_original_cells comp cells (table_valid run routed data k) free
    (fun i member => transfer k i (reg ▸ member))⟩

end SP1Clean.Export.WriteMixedControlTables
