import SP1Clean.Export.InstalledOrdinaryPreset
import SP1Clean.Proofs.Completeness.ObservationCapacity

/-! # Capacity of the four installed ordinary observation tables

The chronological ordinary count demands one padded consumer. The authenticated endpoints
select exactly one terminal row across the empty, nonempty and unrestricted modes.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Machine TraceGen Soundness FormalModel.Shard
open SP1Clean.OrdinaryObservation (Mode history paddedTable terminalInput)
private abbrev consumer := Soundness.OrdinaryObservation.consumer (p := SP1Prime)
private abbrev terminal := Soundness.OrdinaryObservation.terminalComponent (p := SP1Prime)
private abbrev byte := (Channels.byteChannel (p := SP1Prime)).name
private abbrev receipt := (InstructionReceipt.channel (p := SP1Prime)).name
private abbrev link := (SP1Clean.OrdinaryObservation.stateChannel (p := SP1Prime)).name

private theorem observation_channels : rowChannelNames consumer = [byte, byte, byte, byte, receipt, link, link] ∧
    ∀ mode, rowChannelNames (terminal mode) = [link, link] := by
  constructor
  · rw [rowChannelNames, Component.interactions_eq]
    change (((Guarded.main (SP1Clean.OrdinaryObservation.circuit (p := SP1Prime))
      SP1Clean.OrdinaryObservation.guardSupported (varFromOffset SP1Clean.OrdinaryObservation.RowInput 0)).operations (size SP1Clean.OrdinaryObservation.RowInput)).interactions.map _) = _
    rw [Guarded.main_interactions, List.map_map]
    simp only [SP1Clean.OrdinaryObservation.circuit, SP1Clean.OrdinaryObservation.main,
      ClockOrder.circuit, ClockOrder.main, AddOperation.circuit, AddOperation.main,
      WordRangeCheck.circuit, WordRangeCheck.main, Gadgets.ToBits.rangeCheck, Gadgets.toBits, Gadgets.ToBits.main,
      Gadgets.IsZeroField.circuit, Gadgets.Equality.circuit, Gadgets.Equality.main, List.ofFn_succ, List.ofFn_zero,
      GeneralFormalCircuit.toSubcircuit_interactions, FormalCircuit.toSubcircuit_interactions,
      FormalAssertion.toSubcircuit_interactions, circuit_norm, List.map_cons, List.map_nil]
    rfl
  · intro mode
    cases mode <;> simp only [rowChannelNames, Component.interactions_eq, Component.rowOperations, terminal,
      Soundness.OrdinaryObservation.terminalComponent, SP1Clean.OrdinaryObservation.terminal,
      SP1Clean.OrdinaryObservation.terminalEmpty, SP1Clean.OrdinaryObservation.terminalNonempty,
      SP1Clean.OrdinaryObservation.terminalAny, SP1Clean.OrdinaryObservation.emptyMain,
      SP1Clean.OrdinaryObservation.nonemptyMain, SP1Clean.OrdinaryObservation.anyMain,
      Gadgets.IsZeroField.circuit, Gadgets.Equality.circuit, Gadgets.Equality.main, Gadgets.ToBits.rangeCheck, Gadgets.toBits, Gadgets.ToBits.main,
      FormalAssertion.toSubcircuit_interactions, FormalCircuit.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm, List.map_cons, List.map_nil,
      List.ofFn_succ, List.ofFn_zero]

/-- The physical observation heights from the ordinary event count and the authenticated target mode. -/
def observationHeights (ctx : Context) (count : ℕ) (t : Component Fp) : ℕ :=
  slotRows consumer (WitnessGeneration.demandHeight count) t +
    slotRows (terminal (Mode.of ctx.source.sail ctx.target.sail)) 1 t

/-- All four observation components use the released demand-generation mode. -/
theorem observation_targetHeight (state : WitnessGeneration.ComponentState Fp)
    (selected : state.component = Soundness.OrdinaryObservation.consumer ∨
      ∃ mode, state.component = Soundness.OrdinaryObservation.terminalComponent mode) :
    state.targetHeight = WitnessGeneration.demandHeight state.rows.size := by
  cases state with
  | mk component multiplicity operations interactions rows messages =>
    rcases selected with eq | ⟨mode, eq⟩ <;> change component = _ at eq <;> subst component <;>
      exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl

/-- Exact per-channel cost of the real consumer and selected terminal across all four slots.
The endpoint verifier's two link interactions are already counted separately. -/
theorem observation_occurrences (ctx : Context) (count : ℕ) (name : String) :
    let h := WitnessGeneration.demandHeight count
    additionalOccurrences ctx (observationHeights ctx count) name =
      if name = (Channels.byteChannel (p := SP1Prime)).name then 4 * h
      else if name = (InstructionReceipt.channel (p := SP1Prime)).name then h
      else if name = (SP1Clean.OrdinaryObservation.stateChannel (p := SP1Prime)).name then 2 * h + 2 else 0 := by
  obtain ⟨c, t⟩ := observation_registered ctx
  have cost (table : Component Fp) : rowOccurrences table name = (rowChannelNames table).count name := by
    simp [rowOccurrences, rowChannelNames, List.count_eq_countP, List.countP_map, Function.comp_def]
  change additionalOccurrences ctx (fun t => slotRows consumer _ t + slotRows (terminal _) 1 t) name = _
  rw [additionalOccurrences_add, additionalOccurrences_slot _ _ c, additionalOccurrences_slot _ _ (t _),
    cost, cost, observation_channels.1, observation_channels.2]
  let h := WitnessGeneration.demandHeight count
  by_cases b : name = byte
  · subst name
    change h * 4 + 1 * 0 = 4 * h
    omega
  by_cases r : name = receipt
  · subst name
    change h * 1 + 1 * 0 = h
    omega
  by_cases l : name = link
  · subst name
    change h * 2 + 1 * 2 = 2 * h + 2
    omega
  · simp [b, r, l, Ne.symm b, Ne.symm r, Ne.symm l, byte, receipt, link] at *

/-- The selected heights are precisely the ones realized by the four constructed,
constraint-satisfying observation tables of the same complete execution. -/
theorem observation_constructed_heights (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (data : ProverData Fp) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0) ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      ∃ height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size,
      let held := (history (SP1Clean.OrdinaryObservation.startFor (p := SP1Prime) ctx.source.sail) rows).2
      let tables := paddedTable ctx.source.sail rows (WitnessGeneration.demandPadding rows.length) data height ::
        observationTerminalTables (Mode.of ctx.source.sail ctx.target.sail) (terminalInput held) data
      tables.map Table.length = (Soundness.OrdinaryObservation.tables).map (observationHeights ctx rows.length) ∧
        ∀ t ∈ tables, t.Constraints ∧ t.Guarantees := by
  obtain ⟨rows, route, count, _, height, cc, cg, terminals, _⟩ := admissibleExecution_observationWitness execution data
  refine ⟨rows, route, count, height, ?_, ?_⟩
  · rw [List.map_cons, (observation_counts ctx.source.sail ctx.target.sail rows data height).1]
    change _ = (Soundness.OrdinaryObservation.tables).map (fun t => slotRows consumer (WitnessGeneration.demandHeight rows.length) t +
      slotRows (terminal (Mode.of ctx.source.sail ctx.target.sail)) 1 t)
    cases mode : Mode.of ctx.source.sail ctx.target.sail <;> rfl
  · intro table m
    rcases List.mem_cons.mp m with rfl | later
    · exact ⟨cc, cg⟩
    · exact terminals table later

/-- Per-channel reserve for the four observation tables at the native event ceiling. -/
def observationBudget (name : String) : ℕ :=
  if name = byte then 4 * 2 ^ 21
  else if name = receipt then 2 ^ 21
  else if name = link then 2 * 2 ^ 21 + 2 else 0

/-- One consumer bucket fits the actual power-of-two ceiling. Different terminal modes
share one semantic demand across all three physical slots. -/
theorem observation_occurrences_le (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (name : String) :
    additionalOccurrences ctx (observationHeights ctx (events.countP ExecutionEvent.isOrdinary)) name ≤
      observationBudget name := by
  have eventLimit : ctx.limits.events ≤ 2 ^ 21 := preset.1
  have padded := WitnessGeneration.demandHeight_le_pow
    ((List.countP_le_length (p := ExecutionEvent.isOrdinary)).trans (execution.work.1.trans eventLimit))
  rw [observation_occurrences, observationBudget]
  split <;> (repeat' split) <;> omega

private theorem observationBudget_le (name : String) : observationBudget name ≤ 4 * 2 ^ 21 := by
  unfold observationBudget
  split <;> repeat' first | split | decide

/-- Shared capacity for the verifier and 42 installed components on the same semantic path.
The selected allowance preserves the individual caps of every registered channel. -/
theorem fixedProviderPreset_observation_capacity (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤
      SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 - 2 ^ 22 * ordinaryRowBound ch.name - observationBudget ch.name) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0) ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          (observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t + other t))) := by
  apply fixedProviderPreset_ordinary_capacity ctx execution preset
  intro ch registered
  rw [additionalOccurrences_add]
  have used := observation_occurrences_le ctx execution preset ch.name
  have allowed := remaining ch registered
  have maxObservation := observationBudget_le ch.name
  have maxOrdinary := Nat.mul_le_mul_left (2 ^ 22) (ordinaryRowBound_le ch.name)
  have enough : 2 ^ 22 * 126 + 4 * 2 ^ 21 ≤ SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 := by decide
  omega

/-- Every registered channel retains room for at least 285,211,616 further occurrences
after adding the four actual observation components to the 38-table allocation. -/
theorem fixedProviderPreset_observation_fit (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤ 285211616) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0) ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          (observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t + other t))) := by
  apply fixedProviderPreset_observation_capacity ctx execution preset
  intro ch registered
  apply (remaining ch registered).trans
  have maxOrdinary := Nat.mul_le_mul_left (2 ^ 22) (ordinaryRowBound_le ch.name)
  have maxObservation := observationBudget_le ch.name
  have enough : 285211616 ≤ SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 - 2 ^ 22 * 126 - 4 * 2 ^ 21 := by decide
  omega

/-- The verifier and the 42 covered slots fit without further demand or caller-supplied
terminal choices, row counts or verifier bounds. -/
theorem fixedProviderPreset_observation_base_fits (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    ∃ rows, routeObservations? (policy SP1Prime ctx.image) ctx.image.program (fun _ => 0) ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t)) := by
  simpa only [Nat.add_zero] using fixedProviderPreset_observation_fit ctx execution preset (fun _ => 0)
    (by intro ch registered; simp [additionalOccurrences])

end SP1Clean.Export.InstalledAssembly
