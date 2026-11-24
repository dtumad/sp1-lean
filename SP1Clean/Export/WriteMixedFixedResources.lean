import SP1Clean.Export.WriteMixedHostAssembly
import SP1Clean.Proofs.Completeness.MixedSnapshotMembership
import SP1Clean.Proofs.Completeness.MixedProgramFetches

/-! # Installing the counted source-snapshot membership tables

The fixed ROM counts each decoded instruction fetched by the mixed row compiler. The register
and RAM tables count their actual ordered initializer pulls. All three are installed at their
original supervisor positions.
-/

namespace SP1Clean.Export.WriteMixedFixedResources

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WriteSourceRegistry WriteProbe.SparseBoundary

private abbrev F := ZMod SP1Prime

/-- Verifier-fixed providers constructed from the mixed execution. -/
inductive Index
  | program
  | initial (ram : Bool)
  deriving DecidableEq

/-- The actual original position of each fixed resource. -/
def position : Index → ℕ
  | .program => 6
  | .initial ram => if ram then 60 else 59

/-- Identify the fixed resource at a physical supervisor position. -/
def indexAt (i : ℕ) : Option Index := [.program,.initial false,.initial true].find? (fun id => position id == i)

private theorem position_of_indexAt {i : ℕ} {id : Index} (found : indexAt i = some id) : position id = i :=
  eq_of_beq (List.find?_some (p := fun it => position it == i) found)

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

/-- The original named component for each fixed resource. -/
def component : Index → Component F
  | .program => FixedProgramProvider.Preprocessed.component image
  | .initial ram => (members source.sail.memorySnapshot ram).component (members_fit source.sail.memorySnapshot ram)

/-- The counted components coincide with the fixed tables of the actual original verifier. -/
theorem registered_at (id : Index) :
    (base image source target finish).tables[position id]? = some (component image source id) := by
  cases id with
  | program => exact program_at image source target finish
  | initial ram =>
    cases ram <;>
      rw [retained_at _ _ _ _ _ (by decide) (by decide) (by decide), HostFinalMemory.beforeChecks, HostLocalCore.tables,
        List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; decide), List.getElem?_set_ne (by decide)] <;> rfl

private abbrev components := (base image source target finish).tables.drop 6

/-- Original positions still awaiting another physical provider. -/
def Remaining := (i : Fin (components image source target finish).length) →
  sourceAt (6 + i.val) = none → WriteMixedHostTables.indexAt (6 + i.val) = none →
  indexAt (6 + i.val) = none → { t : Table F // t.component = (components image source target finish)[i] }

/-- Installing the fixed Program and two source Memory providers leaves 38 original positions. -/
theorem remaining_count :
    ((List.range' 6 (components image source target finish).length).filter
      (fun i => (sourceAt i).isNone && (WriteMixedHostTables.indexAt i).isNone && (indexAt i).isNone)).length = 38 := by
  rw [List.length_drop, base_length]
  decide

variable {image source target finish} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)

/-- The original reader whose actual cells determine the resource provider's counts. -/
noncomputable def client (ram : Bool) : Table F :=
  let stream := MixedMemoryHistory.stream image source events rows
  let keys := WriteBoundaryBuild.demandKeys events packets
  initialTable source.sail.memorySnapshot ram (terminals source.sail.memorySnapshot stream keys data hint) data
    (terminal_count_fit ram _ _ _ (MixedMemoryHistory.canonical run.1 routed) data hint)

private theorem funded_readers (ram : Bool) :
    ((members source.sail.memorySnapshot ram).readers? ((client run routed data hint packets ram).interactionsWith
      (members source.sail.memorySnapshot ram).channel.toRaw)).isSome := by
  obtain ⟨ids, found, _⟩ := initial_memberships source.sail.memorySnapshot _
    (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram
  exact Option.isSome_iff_exists.mpr ⟨ids, found⟩

private noncomputable def counts (ram : Bool) :=
  let fixed := members source.sail.memorySnapshot ram
  let ledger := (client run routed data hint packets ram).interactionsWith fixed.channel.toRaw
  ReaderCounts.counts ((fixed.readers? ledger).get (funded_readers run routed data hint packets ram))

/-- The complete fixed inventory, including zero-count unused rows and physical padding. -/
private noncomputable def initialProvider (ram : Bool) : Table F :=
  (members source.sail.memorySnapshot ram).buildMembership (members_fit _ ram)
    (fun i => ((counts run routed data hint packets ram)[i] : F)) data

/-- The exact generated provider is locally valid and funds its original initializer ledger. -/
theorem funded (ram : Bool) :
    let fixed := members source.sail.memorySnapshot ram
    let t := initialProvider run routed data hint packets ram
    t.Constraints ∧ t.Guarantees ∧ t.length = fixed.height ∧
      LogUpBalanced (t.interactionsWith fixed.channel.toRaw ++
        (client run routed data hint packets ram).interactionsWith fixed.channel.toRaw) := by
  obtain ⟨indices, selected, valid⟩ := initial_memberships source.sail.memorySnapshot _
    (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram
  change (members source.sail.memorySnapshot ram).readers?
    ((client run routed data hint packets ram).interactionsWith (members source.sail.memorySnapshot ram).channel.toRaw) = some indices at selected
  have chosen := Option.some_get (funded_readers run routed data hint packets ram)
  have eqIds := Option.some.inj (chosen.trans selected)
  simp only [initialProvider, counts, eqIds]
  exact valid

/-- Generate the fixed Program or private snapshot provider from this execution. -/
noncomputable def table : Index → Table F
  | .program => MixedProgramFetches.table run.1 routed data
  | .initial ram => initialProvider run routed data hint packets ram

/-- Every selected table retains its exact original circuit and witness scheduler. -/
theorem table_component (id : Index) : (table run routed data hint packets id).component = component image source id := by
  cases id <;> rfl

private theorem table_valid (id : Index) :
    (table run routed data hint packets id).Constraints ∧ (table run routed data hint packets id).Guarantees := by
  cases id with
  | program => exact ⟨(MixedProgramFetches.funded run.1 routed data).1,(MixedProgramFetches.funded run.1 routed data).2.1⟩
  | initial ram => exact ⟨(funded run routed data hint packets ram).1,(funded run routed data hint packets ram).2.1⟩

/-- Install each generated fixed table at its authenticated position in the supervisor. -/
noncomputable def install (remaining : Remaining image source target finish) :
    WriteMixedHostTables.Remaining image source target finish :=
  fun i absent old => match found : indexAt (6 + i.val) with
    | none => remaining i absent old found
    | some id => ⟨table run routed data hint packets id, by
        have atSlot := registered_at image source target finish id
        rw [position_of_indexAt found, ← List.getElem?_drop, List.getElem?_eq_getElem i.isLt] at atSlot
        exact (table_component run routed data hint packets id).trans (Option.some.inj atSlot).symm⟩

/-- Each generated resource slot discharges its own local constraints and guarantees. -/
theorem install_valid (remaining : Remaining image source target finish)
    (checked : ∀ i absent old missing, let t := (remaining i absent old missing).1; t.Constraints ∧ t.Guarantees) :
    ∀ i absent old, let t := (install run routed data hint packets remaining i absent old).1; t.Constraints ∧ t.Guarantees := by
  intro i absent old
  dsimp only [install]
  split
  · exact checked i absent old _
  · exact table_valid run routed data hint packets _

end SP1Clean.Export.WriteMixedFixedResources
