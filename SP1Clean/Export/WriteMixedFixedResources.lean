import SP1Clean.Export.WriteMixedHostAssembly
import SP1Clean.Proofs.Completeness.MixedTargetMembership
import SP1Clean.Proofs.Completeness.MixedProgramFetches

/-! # Installing the counted ROM and snapshot tables

The fixed ROM counts each decoded instruction fetched by the mixed row compiler. The register
and RAM memberships at both endpoints count their actual signed client ledger. The target
checkers consume each terminal with its actual outgoing Sail word and snapshot change selector.
-/

namespace SP1Clean.Export.WriteMixedFixedResources

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WriteSourceRegistry WriteProbe.SparseBoundary

private abbrev F := ZMod SP1Prime

/-- Verifier-fixed providers constructed from the mixed execution. -/
inductive Index
  | program
  | initial (ram : Bool)
  | check (ram : Bool)
  | final (ram : Bool)
  deriving DecidableEq

/-- The actual original position of each fixed resource. -/
def position : Index → ℕ
  | .program => 6
  | .initial ram => if ram then 60 else 59
  | .check ram => if ram then 95 else 94
  | .final ram => if ram then 97 else 96

/-- Identify the fixed resource at a physical supervisor position. -/
def indexAt (i : ℕ) : Option Index :=
  [.program,.initial false,.initial true,.check false,.check true,.final false,.final true].find? (fun id => position id == i)

private theorem position_of_indexAt {i : ℕ} {id : Index} (found : indexAt i = some id) : position id = i :=
  eq_of_beq (List.find?_some (p := fun it => position it == i) found)

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

/-- The original named component for each fixed resource. -/
def component : Index → Component F
  | .program => FixedProgramProvider.Preprocessed.component image
  | .initial ram => (members source.sail.memorySnapshot ram).component (members_fit source.sail.memorySnapshot ram)
  | .check ram => MixedTargetMemory.checkComponent target.sail.memorySnapshot ram
  | .final ram => (MixedTargetMemory.targetMembers target.sail.memorySnapshot ram).component (MixedTargetMemory.targetMembers_fit _ ram)

/-- The counted components coincide with the fixed tables of the actual original verifier. -/
theorem registered_at (id : Index) :
    (base image source target finish).tables[position id]? = some (component image source target id) := by
  cases id with
  | program => exact program_at image source target finish
  | initial ram =>
    cases ram <;>
      rw [retained_at _ _ _ _ _ (by decide) (by decide) (by decide), HostFinalMemory.beforeChecks, HostLocalCore.tables,
        List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; decide), List.getElem?_set_ne (by decide)] <;> rfl
  | check ram =>
    cases ram
    · exact target_check_at image source target finish 0
    · exact target_check_at image source target finish 1
  | final ram =>
    cases ram
    · exact target_check_at image source target finish 2
    · exact target_check_at image source target finish 3

private abbrev components := (base image source target finish).tables.drop 6

/-- Original positions still awaiting another physical provider. -/
def Remaining := (i : Fin (components image source target finish).length) →
  sourceAt (6 + i.val) = none → WriteMixedHostTables.indexAt (6 + i.val) = none →
  indexAt (6 + i.val) = none → { t : Table F // t.component = (components image source target finish)[i] }

/-- Installing the Program and source/target Memory resources leaves 34 original positions. -/
theorem remaining_count :
    ((List.range' 6 (components image source target finish).length).filter
      (fun i => (sourceAt i).isNone && (WriteMixedHostTables.indexAt i).isNone && (indexAt i).isNone)).length = 34 := by
  rw [List.length_drop, base_length]
  decide

variable {image source target finish} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)

/-- The fixed register or eight-byte RAM membership inventory for one endpoint. -/
private def fixed (source target : ExecutionSnapshot) (closing ram : Bool) : StaticTable F (MembershipRow ram) :=
  if closing then MixedTargetMemory.targetMembers target.sail.memorySnapshot ram else members source.sail.memorySnapshot ram

private theorem fixed_fits (source target : ExecutionSnapshot) (closing ram : Bool) :
    (fixed source target closing ram).height < UInt64.size := by
  cases closing
  · exact members_fit _ ram
  · exact MixedTargetMemory.targetMembers_fit _ ram

/-- The original checker or initializer supplying the actual signed reads for the fixed table. -/
noncomputable def client (closing ram : Bool) : Table F :=
  let keys := WriteBoundaryBuild.demandKeys events packets
  if closing then MixedTargetMemory.fromExecution run.1 routed keys data hint ram else
    let stream := MixedMemoryHistory.stream image source events rows
    initialTable source.sail.memorySnapshot ram (terminals source.sail.memorySnapshot stream keys data hint) data
      (terminal_count_fit ram _ _ _ (MixedMemoryHistory.canonical run.1 routed) data hint)

private theorem readers (closing ram : Bool) :
    let t := fixed source target closing ram
    let c := client run routed data hint packets closing ram
    ∃ ids, t.readers? (c.interactionsWith t.channel.toRaw) = some ids ∧
      let provider := t.buildMembership (fixed_fits source target closing ram) (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      provider.Constraints ∧ provider.Guarantees ∧ provider.length = t.height ∧
        LogUpBalanced (provider.interactionsWith t.channel.toRaw ++ c.interactionsWith t.channel.toRaw) := by
  cases closing
  · exact initial_memberships source.sail.memorySnapshot _ (WriteBoundaryBuild.demandKeys events packets)
      (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram
  · exact MixedTargetMemory.target_memberships run.1 routed (WriteBoundaryBuild.demandKeys events packets) data hint ram

private theorem funded_readers (closing ram : Bool) :
    let t := fixed source target closing ram
    (t.readers? ((client run routed data hint packets closing ram).interactionsWith t.channel.toRaw)).isSome := by
  obtain ⟨ids, found, _⟩ := readers run routed data hint packets closing ram
  exact Option.isSome_iff_exists.mpr ⟨ids, found⟩

/-- Allocate every physical membership count using the original source or target reader. -/
private noncomputable def provider (closing ram : Bool) : Table F :=
  let t := fixed source target closing ram
  let ledger := (client run routed data hint packets closing ram).interactionsWith t.channel.toRaw
  let ids := (t.readers? ledger).get (funded_readers run routed data hint packets closing ram)
  t.buildMembership (fixed_fits _ _ closing ram) (fun i => ((ReaderCounts.counts ids)[i] : F)) data

/-- Every original snapshot provider is locally valid and funds its entire client ledger. -/
theorem funded (closing ram : Bool) :
    let t := fixed source target closing ram
    let physical := provider run routed data hint packets closing ram
    physical.Constraints ∧ physical.Guarantees ∧ physical.length = t.height ∧
      LogUpBalanced (physical.interactionsWith t.channel.toRaw ++
        (client run routed data hint packets closing ram).interactionsWith t.channel.toRaw) := by
  obtain ⟨ids, selected, valid⟩ := readers run routed data hint packets closing ram
  have chosen := Option.some_get (funded_readers run routed data hint packets closing ram)
  have eqIds := Option.some.inj (chosen.trans selected)
  simp only [provider, eqIds]
  exact valid

/-- Generate the fixed Program or private snapshot provider from this execution. -/
noncomputable def table : Index → Table F
  | .program => MixedProgramFetches.table run.1 routed data
  | .initial ram => provider run routed data hint packets false ram
  | .check ram => client run routed data hint packets true ram
  | .final ram => provider run routed data hint packets true ram

/-- Every selected table retains its exact original circuit and witness scheduler. -/
theorem table_component (id : Index) : (table run routed data hint packets id).component = component image source target id := by
  cases id with
  | program | initial | final => rfl
  | check ram => cases ram <;> rfl

private theorem table_valid (id : Index) :
    (table run routed data hint packets id).Constraints ∧ (table run routed data hint packets id).Guarantees := by
  cases id with
  | program => exact ⟨(MixedProgramFetches.funded run.1 routed data).1,(MixedProgramFetches.funded run.1 routed data).2.1⟩
  | initial ram => exact ⟨(funded run routed data hint packets false ram).1,(funded run routed data hint packets false ram).2.1⟩
  | check ram => exact MixedTargetMemory.fromExecution_valid run.1 routed _ data hint ram
  | final ram => exact ⟨(funded run routed data hint packets true ram).1,(funded run routed data hint packets true ram).2.1⟩

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
