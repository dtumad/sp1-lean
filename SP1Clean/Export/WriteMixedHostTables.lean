import SP1Clean.Export.WriteMixedHostRegistry
import SP1Clean.Export.WriteMixedSourceRecords
import SP1Clean.Proofs.Completeness.MixedCommitLedger
import SP1Clean.Proofs.Completeness.ExecutionObservationEndpoint

/-! # Installing the commitment and ordinary observation witnesses in the original supervisor

All 22 tables come from the actual mixed execution. The residual provider family ranges only
over positions left open by the boundary, Memory, commitment and ordinary observation compilers.
-/

namespace SP1Clean.Export.WriteMixedHostTables

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WitnessGeneration
open SP1Clean.OrdinaryObservation (startFor history terminalInput Mode paddedTable)

private abbrev F := ZMod SP1Prime

variable {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events)

/-- The ordered physical inputs of a commitment bank. -/
def bankRows (d : Bool) : List CommitBanks.Entry :=
  (CommitBanks.rows? d 0 (source.host.bank d) (CommitBanks.calls d events)).get (by
    obtain ⟨rows, routed, _⟩ := CommitBanks.of_execution run d
    exact Option.isSome_iff_exists.mpr ⟨rows,routed⟩)

theorem bankRows_eq (d : Bool) :
    CommitBanks.rows? d 0 (source.host.bank d) (CommitBanks.calls d events) = some (bankRows run d) :=
  (Option.some_get _).symm

private def lastState (d : Bool) (events : List ExecutionEvent) (target : ExecutionSnapshot) :=
  CommitBanks.stateAt ((CommitBanks.calls d events).foldl (fun _ c => c.clock) 0) (target.host.bank d)

private theorem bankFacts (d : Bool) :
    (∀ r ∈ bankRows run d, HostCommitChip.ProverAssumptions d r.1 r.2) ∧
    (bankRows run d).map (fun r => r.2.call) = (CommitBanks.calls d events).map CommitBanks.message ∧
    HostCommitBoundary.TerminalSpec (lastState d events target) := by
  obtain ⟨rs, routed, valid, handoff, last, _⟩ := CommitBanks.of_execution run d
  obtain rfl := Option.some.inj ((bankRows_eq run d).symm.trans routed)
  exact ⟨valid, handoff, last⟩

theorem bankLaneFits (d : Bool) (slot : Fin 8) :
    demandHeight (CommitBanks.lane slot (bankRows run d)).length ≤ UInt64.size :=
  CommitBanks.lane_fits run d (bankFacts run d).2.1 slot

private def builtBank (d : Bool) (data : ProverData F) :=
  CommitBanks.bankTable d (bankRows run d) (lastState d events target) data
    (bankLaneFits run d)

private noncomputable def ordinaryRows : List RoutedEvent :=
  (routeObservations? (policy SP1Prime image) image.program (fun _ => 0) source.realize events).get (by
    obtain ⟨rs, emitted, _⟩ := admissibleExecution_routeObservations run
    exact Option.isSome_iff_exists.mpr ⟨rs,emitted⟩)

private theorem ordinaryRows_eq :
    routeObservations? (policy SP1Prime image) image.program (fun _ => 0) source.realize events = some (ordinaryRows run) :=
  (Option.some_get _).symm

private theorem ordinaryFits :
    (ordinaryRows run).length + demandPadding (ordinaryRows run).length ≤ UInt64.size := by
  obtain ⟨rs, emitted, _, _, fit, _⟩ := admissibleExecution_observationWitness run (.empty _)
  obtain rfl := Option.some.inj ((ordinaryRows_eq run).symm.trans emitted)
  exact fit

private noncomputable def ordinaryTables (data : ProverData F) : List (Table F) :=
  let rows := ordinaryRows run
  let start := startFor (p := SP1Prime) source.sail
  let input := terminalInput (history start rows).2
  paddedTable source.sail rows (demandPadding rows.length) data (ordinaryFits run) ::
    observationTerminalTables (Mode.of source.sail target.sail) input data

private theorem ordinary_valid (data : ProverData F) :
    ∀ t ∈ ordinaryTables run data, t.Constraints ∧ t.Guarantees := by
  obtain ⟨rs, emitted, _, _, _, cc, cg, terms, _⟩ := admissibleExecution_observationWitness run data
  obtain rfl := Option.some.inj ((ordinaryRows_eq run).symm.trans emitted)
  intro t used
  rcases List.mem_cons.mp used with rfl | mem
  · exact ⟨cc,cg⟩
  · exact terms _ mem

variable (data : ProverData F)

/-- The canonical physical table selected at every bank and observation position. -/
noncomputable def table : Index → Table F
  | .bank d i => builtBank run d data i
  | .observation i => (ordinaryTables run data)[i.val]'i.isLt

theorem registered (id : Index) : (table run data id).component = component id := by
  cases id with
  | bank d i => exact CommitBanks.bankTable_component ..
  | observation i =>
    fin_cases i <;> rfl

theorem valid (id : Index) : (table run data id).Constraints ∧ (table run data id).Guarantees := by
  cases id with
  | bank d i => cases i with
    | none => exact CommitBanks.terminalTable_valid _ _ _ (bankFacts run d).2.2
    | some slot =>
      exact CommitBanks.laneTable_valid d slot _ data
        (bankLaneFits run d slot) (bankFacts run d).1
  | observation i => exact ordinary_valid run data _ (List.getElem_mem i.isLt)

/-- Both mutable bank channels close against the full incoming and outgoing host snapshots
on the actual physical commitment tables. -/
theorem bank_state_balanced (d : Bool) :
    LogUpBalanced ([(HostCommitChip.stateChannel d).pushedValue (HostCommitBoundary.start (HostCommitEnsemble.sourceValues d source.host)),
      (HostCommitChip.stateChannel d).pulledValue (HostCommitBoundary.final (HostCommitEnsemble.sourceValues d target.host))] ++
      HostCommitBank.indices.flatMap (fun i => (table run data (.bank d i)).interactionsWith (HostCommitChip.stateChannel d).toRaw)) := by
  obtain ⟨rs, emitted, _, _, _, chain⟩ := CommitBanks.of_execution run d
  obtain rfl := Option.some.inj ((bankRows_eq run d).symm.trans emitted)
  exact CommitBanks.state_balanced d (bankRows run d) _ (lastState d events target) data
    (bankLaneFits run d) chain

end SP1Clean.Export.WriteMixedHostTables
