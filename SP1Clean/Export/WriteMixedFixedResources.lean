import SP1Clean.Export.WriteMixedHostAssembly
import SP1Clean.Proofs.Completeness.MixedSnapshotMembership

/-! # Installing the counted source-snapshot membership tables

The fixed register and RAM tables read their multiplicities directly from the two ordered
initializers compiled for this segment. Their distinct positions in the native supervisor
are discharged before the remaining original providers are assembled.
-/

namespace SP1Clean.Export.WriteMixedFixedResources

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WriteSourceRegistry WriteProbe.SparseBoundary

private abbrev F := ZMod SP1Prime

/-- The actual original register and RAM membership provider positions. -/
def position (ram : Bool) : ℕ := if ram then 60 else 59

/-- Identify the source-snapshot membership provider installed at a physical index. -/
def indexAt (i : ℕ) : Option Bool := [false,true].find? (fun ram => position ram == i)

private theorem position_of_indexAt {i : ℕ} {ram : Bool} (found : indexAt i = some ram) : position ram = i :=
  eq_of_beq (List.find?_some (p := fun r => position r == i) found)

variable (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F)

/-- The two counted components are exactly the verifier's original fixed tables. -/
theorem registered_at (ram : Bool) :
    (base image source target finish).tables[position ram]? =
      some ((members source.sail.memorySnapshot ram).component (members_fit source.sail.memorySnapshot ram)) := by
  cases ram <;>
    rw [retained_at _ _ _ _ _ (by decide) (by decide) (by decide), HostFinalMemory.beforeChecks, HostLocalCore.tables,
      List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; decide), List.getElem?_set_ne (by decide)] <;> rfl

private abbrev components := (base image source target finish).tables.drop 6

/-- Original positions still awaiting another physical provider. -/
def Remaining := (i : Fin (components image source target finish).length) →
  sourceAt (6 + i.val) = none → WriteMixedHostTables.indexAt (6 + i.val) = none →
  indexAt (6 + i.val) = none → { t : Table F // t.component = (components image source target finish)[i] }

/-- Installing both original source membership tables leaves 39 original positions. -/
theorem remaining_count :
    ((List.range' 6 (components image source target finish).length).filter
      (fun i => (sourceAt i).isNone && (WriteMixedHostTables.indexAt i).isNone && (indexAt i).isNone)).length = 39 := by
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
noncomputable def table (ram : Bool) : Table F :=
  (members source.sail.memorySnapshot ram).buildMembership (members_fit _ ram)
    (fun i => ((counts run routed data hint packets ram)[i] : F)) data

/-- The exact generated provider is locally valid and funds its original initializer ledger. -/
theorem funded (ram : Bool) :
    let fixed := members source.sail.memorySnapshot ram
    let t := table run routed data hint packets ram
    t.Constraints ∧ t.Guarantees ∧ t.length = fixed.height ∧
      LogUpBalanced (t.interactionsWith fixed.channel.toRaw ++
        (client run routed data hint packets ram).interactionsWith fixed.channel.toRaw) := by
  obtain ⟨indices, selected, valid⟩ := initial_memberships source.sail.memorySnapshot _
    (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram
  change (members source.sail.memorySnapshot ram).readers?
    ((client run routed data hint packets ram).interactionsWith (members source.sail.memorySnapshot ram).channel.toRaw) = some indices at selected
  have chosen := Option.some_get (funded_readers run routed data hint packets ram)
  have eqIds := Option.some.inj (chosen.trans selected)
  simp only [table, counts, eqIds]
  exact valid

/-- Fill both provider slots in the 41-position assembly from their original client tables. -/
noncomputable def install (remaining : Remaining image source target finish) :
    WriteMixedHostTables.Remaining image source target finish :=
  fun i absent old => match found : indexAt (6 + i.val) with
    | none => remaining i absent old found
    | some ram => ⟨table run routed data hint packets ram, by
        have atSlot := registered_at image source target finish ram
        rw [position_of_indexAt found, ← List.getElem?_drop, List.getElem?_eq_getElem i.isLt] at atSlot
        exact (Option.some.inj atSlot).symm⟩

/-- The two generated resource slots independently discharge their local constraints and guarantees. -/
theorem install_valid (remaining : Remaining image source target finish)
    (checked : ∀ i absent old missing, let t := (remaining i absent old missing).1; t.Constraints ∧ t.Guarantees) :
    ∀ i absent old, let t := (install run routed data hint packets remaining i absent old).1; t.Constraints ∧ t.Guarantees := by
  intro i absent old
  dsimp only [install]
  split
  · exact checked i absent old _
  · exact ⟨(funded run routed data hint packets _).1,(funded run routed data hint packets _).2.1⟩

end SP1Clean.Export.WriteMixedFixedResources
