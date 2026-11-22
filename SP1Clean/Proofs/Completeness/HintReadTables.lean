import SP1Clean.Proofs.Completeness.HintReadTransfers
import SP1Clean.Proofs.Completeness.HintReadCapacity
import SP1Clean.Soundness.HintReadWriteLedger
import ToClean.Air.TableBuild

/-! # Generating the two installed HINT_READ word tables

The native tape fixes every active transfer. Rows are collected by table variant before each
table is padded to Clean's demand height, so the empty case stays empty. Access reconstruction
uses the noncomputable ordinary-transition projection in the mixed prefix compiler.
-/

namespace SP1Clean.TraceGen.HintReadTransfers
open Semantics Machine FormalModel.Shard HintQueue Soundness.Target
open Circuit Air.Flat Soundness HintReadWordChip

private abbrev F := ZMod SP1Prime
private abbrev Entry := Bool × RowInput F

/-- Physical inputs of the event at a genuine tape position. Successful calls other than
HINT_READ contribute no word transfers. -/
noncomputable def rowsAt? (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (cut : ℕ) : Option (List Entry) := do
  let event ← events[cut]?
  match event with
  | .ordinary => return []
  | .syscall call =>
    if call.rawCode = SyscallKind.hintRead.code then
      let hostPolicy := policy SP1Prime image
      let (current, frontier) ← mixedAccessPrefix hostPolicy image.program source.realize events cut
      let (store, pointer) ← storeAfter? hostPolicy image.program source.realize (events.take cut) (ofList source.host.io.hints)
      let node ← node? store pointer
      return (Request.mk call.clock pointer call.arg1.toNat node.bytes).rows frontier current.sail
    else return []

/-- The complete word inputs in execution order, before table bucketing. -/
noncomputable def history (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) :
    List Entry :=
  (List.finRange events.length).flatMap fun position => (rowsAt? image source events position.val).getD []

private def markersFor (event : ExecutionEvent) : List Bool :=
  ((HintReadDemand.length? event).map fun n => List.replicate (n / 8) false ++ [true]).getD []

private def Honest (entry : Entry) : Prop :=
  entry.2.2 = 1 ∧ ∀ data hint, (circuit entry.1).ProverAssumptions entry.2 data hint

private theorem rowsAt_complete {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {event : ExecutionEvent} (present : events[cut]? = some event) :
    ∃ rows, rowsAt? image source events cut = some rows ∧ rows.map Prod.fst = markersFor event ∧
      ∀ entry ∈ rows, Honest entry := by
  cases event with
  | ordinary => exact ⟨[], by simp [rowsAt?, present], rfl, by simp⟩
  | syscall call =>
    by_cases read : call.rawCode = SyscallKind.hintRead.code
    · obtain ⟨current, _, frontier, cursor, _, bytes, _, _, built, _, queueBuilt, _, node, _, _, _, length,
        _, _, valid⟩ := of_admissibleExecution execution present read
      let request : Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
      refine ⟨request.rows frontier current.sail, ?_, ?_, ?_⟩
      · simp [rowsAt?, present, read, built, queueBuilt, node, request]
      · rw [Request.markers]
        simp [markersFor, HintReadDemand.length?, read, request, length]
      · intro entry member
        obtain ⟨index, bound, position⟩ := List.getElem_of_mem member
        have pos : index < wordCount bytes := by simpa only [Request.rows_length, request] using bound
        have info := valid index pos
        obtain ⟨got, active, _, _, _, _, _, _, assumptions⟩ := info
        rw [List.getElem?_eq_getElem bound, position] at got
        cases Option.some.inj got
        exact ⟨active, assumptions⟩
    · exact ⟨[], by simp [rowsAt?, present, read], by simp [markersFor, HintReadDemand.length?, read], by simp⟩

private theorem history_complete {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    (history image source events).map Prod.fst = events.flatMap markersFor ∧
      ∀ entry ∈ history image source events, Honest entry := by
  constructor
  · rw [history, List.map_flatMap]
    conv_rhs => rw [← List.map_getElem_finRange events, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    obtain ⟨rows, success, markers, _⟩ := rowsAt_complete execution (List.getElem?_eq_getElem i.isLt)
    simpa only [success, Option.getD_some] using markers
  · intro entry member
    obtain ⟨i, _, occurs⟩ := List.mem_flatMap.mp member
    obtain ⟨rows, success, _, correct⟩ := rowsAt_complete execution (List.getElem?_eq_getElem i.isLt)
    rw [success] at occurs
    exact correct entry occurs

/-- Inputs in a single physical variant, before applying demand padding. -/
def selected (last : Bool) (entries : List Entry) : List (RowInput F) :=
  (entries.filter fun entry => entry.1 == last).map Prod.snd

private theorem count_markers (events : List ExecutionEvent) (last : Bool) :
    (events.flatMap markersFor).count last =
      if last then (events.filterMap HintReadDemand.length?).length else HintReadDemand.continuing (events.filterMap HintReadDemand.length?) := by
  induction events with
  | nil => cases last <;> simp [HintReadDemand.continuing]
  | cons first rest ih =>
    cases h : HintReadDemand.length? first <;> cases last <;>
      simp_all [markersFor, HintReadDemand.continuing, List.count_replicate]

/-- The dynamic compiler produces the exact two heights used by the physical capacity bound. -/
theorem selected_length {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) (last : Bool) :
    (selected last (history image source events)).length =
      if last then (events.filterMap HintReadDemand.length?).length else HintReadDemand.continuing (events.filterMap HintReadDemand.length?) := by
  rw [← count_markers, ← (history_complete execution).1, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  simp [selected, Function.comp_def]

/-- Physical inputs retain the zero row in every demand-padding position. -/
def physicalInputs (last : Bool) (entries : List Entry) : List (RowInput F) :=
  let inputs := selected last entries
  inputs ++ List.replicate (WitnessGeneration.demandPadding inputs.length) 0

theorem physicalInputs_length (last : Bool) (entries : List Entry) :
    (physicalInputs last entries).length = WitnessGeneration.demandHeight (selected last entries).length := by
  simp [physicalInputs, WitnessGeneration.add_demandPadding]

/-- Use Clean's row builder on the named input data of the installed guarded word component. -/
def wordTable (last : Bool) (entries : List Entry) (data : ProverData F)
    (height : WitnessGeneration.demandHeight (selected last entries).length ≤ UInt64.size) : Table F :=
  let rows := physicalInputs last entries
  let component := HintReadCoverage.component (p := SP1Prime) last
  Table.build component rows (component.inputData rows data) (.empty _)
    ((physicalInputs_length last entries).trans_le height) (by trivial) (component.inputData_consistent rows data)

/-- The table height counts the full physical demand, including every inactive row. -/
theorem wordTable_length (last : Bool) (entries : List Entry) (data : ProverData F) (height) :
    (wordTable last entries data height).length = WitnessGeneration.demandHeight (selected last entries).length := by
  change (_root_.List.map _ (physicalInputs last entries)).length = _
  exact (List.length_map ..).trans (physicalInputs_length last entries)

private theorem table_ledger (last : Bool) (entries : List Entry) (data : ProverData F) (height)
    (channel : RawChannel F) (values : RowInput F → List (Interaction F))
    (point : ∀ env, (HintReadCoverage.component last).operations.interactionValuesWith channel env =
      values (valueFromOffset RowInput 0 env)) :
    (wordTable last entries data height).interactionsWith channel = (physicalInputs last entries).flatMap values := by
  let c := HintReadCoverage.component (p := SP1Prime) last
  let rows := physicalInputs last entries
  let own := c.inputData rows data
  let evaluated := fun physical => c.operations.interactionValuesWith channel (Environment.fromArray physical own)
  let build := fun input => c.buildRow input own (ProverHint.empty _)
  change (rows.map build).flatMap evaluated = rows.flatMap values
  refine (List.flatMap_map build evaluated rows).trans ?_
  apply List.flatMap_congr
  intro row _
  have read := c.rowInput_buildRow row own own (ProverHint.empty _)
  change valueFromOffset RowInput 0 (Environment.fromArray (build row) own) = row at read
  exact (point _).trans (congrArg values read)

/-- The exact signed private-cursor ledger retains two occurrences per physical row. -/
theorem wordTable_cursors (last : Bool) (entries : List Entry) (data : ProverData F) (height) :
    (wordTable last entries data height).interactionsWith stateChannel.toRaw =
      (physicalInputs last entries).flatMap fun row =>
        [stateChannel.pulledIfValue row.2 row.1.previous, stateChannel.pushedIfValue row.2 row.1.next] := by
  apply table_ledger
  intro env
  have eq := (HintReadCoverage.view (p := SP1Prime) last).interactions env
  rw [HintReadCoverage.view_activity, Guarded.eval_activity, eval_varFromOffset_valueFromOffset] at eq
  exact eq

private theorem row_activity (last : Bool) (env : Environment F) :
    HintReadCoverage.rowActivity (last, env) = (valueFromOffset RowInput 0 env).2 := by
  rw [← eval_varFromOffset_valueFromOffset RowInput 0 env]
  simpa only [HintReadCoverage.rowActivity, varFromOffset_pair, Nat.zero_add] using
    Guarded.eval_activity env (varFromOffset RowInput 0)

/-- Each physical word row supplies its actual signed Memory predecessor and successor,
including both zero-weight entries of inactive padding. -/
theorem wordTable_memory (last : Bool) (entries : List Entry) (data : ProverData F) (height) :
    (wordTable last entries data height).interactionsWith Channels.memoryChannel.toRaw =
      (physicalInputs last entries).flatMap fun row =>
        [Channels.memoryChannel.pulledIfValue row.2 row.1.ram.prior,
          Channels.memoryChannel.pushedIfValue row.2 row.1.ram.pushed] := by
  apply table_ledger
  intro env
  have eq := HintReadWriteLedger.row_memory_values (p := SP1Prime) (last, env)
  rw [row_activity] at eq
  exact eq

/-- Every physical row retains all eight byte-permission requests, including the padding word
and all zero-multiplicity requests from disabled physical rows. -/
theorem wordTable_permissions (last : Bool) (entries : List Entry) (data : ProverData F) (height) :
    (wordTable last entries data height).interactionsWith WritePermissionProvider.channel.toRaw =
      (physicalInputs last entries).flatMap fun row =>
        List.ofFn (fun index : Fin 8 => WritePermissionProvider.channel.pulledIfValue row.2
          (Address.offset row.1.address (index.val : F))) := by
  apply table_ledger
  intro env
  have eq := HintReadWriteLedger.row_permission_values (p := SP1Prime) (last, env)
  rw [row_activity] at eq
  exact eq

/-- Both variants have kernel-checked constraints and guarantees for the actual full tape and
their exact independently rounded heights, with no supplied row evidence or height bound. -/
theorem tables_of_admissibleExecution {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (last : Bool) (data : ProverData F) :
    let entries := history image source events
    ∃ height, (wordTable last entries data height).Constraints ∧ (wordTable last entries data height).Guarantees := by
  let entries := history image source events
  have honest := (history_complete execution).2
  let lengths := events.filterMap HintReadDemand.length?
  have charge := HintReadDemand.writeBytes execution.1.2
  have paid := execution.2.2.1 .writeBytes
  change _ ≤ SP1Prime - 1 at paid
  have small : (selected last entries).length ≤ SP1Prime - 1 := by
    rw [show (selected last entries).length = _ from selected_length execution last]
    split <;> omega
  have height := (WitnessGeneration.demandHeight_bounds (selected last entries).length).2.trans (Nat.mul_le_mul_left 2 small)
  refine ⟨height.trans (by decide), ?_⟩
  let rows := physicalInputs last entries
  let component := HintReadCoverage.component (p := SP1Prime) last
  have valid (row : RowInput F) (member : row ∈ rows) :
      (circuit last).ProverAssumptions row (component.inputData rows data) (ProverHint.empty _) := by
    rcases List.mem_append.mp member with occurs | pad
    · obtain ⟨entry, inFilter, rfl⟩ := List.mem_map.mp occurs
      obtain ⟨active, selectedEntry⟩ := List.mem_filter.mp inFilter
      have variant : entry.1 = last := beq_iff_eq.mp selectedEntry
      rw [← variant]
      exact (honest entry active).2 _ _
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp pad
      exact ⟨Or.inl rfl, fun impossible => (zero_ne_one impossible).elim⟩
  unfold wordTable
  constructor
  · apply Table.build_constraints
    exact valid
  · apply Table.build_guarantees
    exact valid

end SP1Clean.TraceGen.HintReadTransfers
