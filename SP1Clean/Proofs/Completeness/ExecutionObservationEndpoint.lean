import SP1Clean.Proofs.Completeness.ExecutionObservationSuccessor
import SP1Clean.FormalModel.ShardRetirement

/-! # Constructing the public ordinary-observation endpoint of a mixed execution

The installed terminal consumes the final held observation from the chronological instruction
tape. The complete semantic endpoint fixes its mode, its normalized PC, and its wrapping
retirement counter, including empty and host-only segments.
-/

namespace SP1Clean.TraceGen
open Circuit Air.Flat Semantics Machine FormalModel.Shard OrdinaryObservation Soundness.Target
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
private theorem history_walk (initial : State (ZMod p)) (rows : List RoutedEvent) :
    let result := history initial rows
    Soundness.Walk.IsWalk Soundness.OrdinaryObservation.edge initial result.2 result.1 := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rest ih =>
    exact ⟨rfl, ih (populate initial row.rawPushState.toMessage).next⟩

omit [Fact (2 ^ 25 < p)] in
private theorem history_word (initial : State (ZMod p)) (rows : List RoutedEvent)
    (bounded : Word.isU64 initial.counter)
    (valid : ∀ input ∈ (history initial rows).1, Spec input) : Word.isU64 (history initial rows).2.counter := by
  induction rows generalizing initial with
  | nil => exact bounded
  | cons row rest ih =>
    let input := populate initial row.rawPushState.toMessage
    have head := valid input (List.mem_cons_self ..)
    exact ih input.next head.2.2.2.1 (fun later member => valid later (.tail input member))

private theorem enabled_realize (source : SailSnapshot) :
    retirementEnabled source.realize = retirementEnabled source.skeleton := by
  unfold retirementEnabled
  rfl

private theorem refresh_realize (source : SailSnapshot) :
    TryStepReduction.refreshedMip source.realize = TryStepReduction.refreshedMip source.skeleton := by
  unfold TryStepReduction.refreshedMip
  rfl

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem mode_accepts {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    (dynamic : DynamicMatch source target events) :
    (Mode.of source.sail target.sail).AcceptsCount (events.countP ExecutionEvent.isOrdinary) := by
  apply Mode.of_acceptsCount
  · intro empty
    exact (quiet_iff _ _).mpr ⟨by rw [dynamic.increment, ite_eq_left empty],
      by rw [dynamic.interrupts, ite_eq_left empty], by rw [dynamic.eventIndex, ite_eq_left empty],
      dynamic.nextPC.trans (nextPcAfter_of_countP_ordinary_eq_zero _ _ empty)⟩
  · intro active
    exact (refreshed_iff _ _).mpr ⟨by rw [dynamic.increment, ite_eq_right active, enabled_realize],
      by rw [dynamic.interrupts, ite_eq_right active, refresh_realize], by rw [dynamic.eventIndex, ite_eq_right active],
      Executes.nextPC_bounded execution active⟩

private theorem held_counter {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (sourceValid : ExecutionSourceValid image source) (dynamic : DynamicMatch source target events)
    (rows : List RoutedEvent) (count : rows.length = events.countP ExecutionEvent.isOrdinary)
    (valid : ∀ input ∈ (history (startFor (p := p) source.sail) rows).1, Spec input) :
    let held := (history (startFor (p := p) source.sail) rows).2
    held.counter = (finalFor (p := p) source.sail target.sail).counter ∧ held.enabled = (startFor (p := p) source.sail).enabled := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  let start := startFor (p := p) source.sail
  let final := finalFor (p := p) source.sail target.sail
  let held := (history start rows).2
  obtain ⟨flag, sum⟩ := Soundness.OrdinaryObservation.counter_of_walk start held (history start rows).1 valid
    (history_walk start rows)
  rw [history_length, count, startFor_enabled_count] at sum
  have initial : Word.toBitVec64 start.counter = (source.sail.registers.get? Register.minstret).getD 0 := toBitVec64_bitVecToWord _
  have finalWord : Word.toBitVec64 final.counter = (target.sail.registers.get? Register.minstret).getD 0 := toBitVec64_bitVecToWord _
  have present := Std.ExtDHashMap.get?_eq_some_get (sourceValid.2.1.init Register.minstret)
  change source.sail.registers.get? Register.minstret = some _ at present
  refine ⟨Word.eq_of_toBitVec64_eq (history_word start rows (isU64_bitVecToWord _) valid) (isU64_bitVecToWord _) ?_, flag⟩
  rw [sum, initial, show Word.toBitVec64 (finalFor (p := p) source.sail target.sail).counter = _ from finalWord,
    dynamic.retired, present]
  rfl

/-- The true semantic endpoints construct the physical table in the target-selected mode.
The actual terminal push matches the supplied PC, counter, enable and sentinel clock. -/
theorem admissibleExecution_observationEndpoint {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (data : ProverData (ZMod p)) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      let mode := Mode.of source.sail target.sail
      let held := (history (startFor (p := p) source.sail) rows).2
      let input := terminalInput held
      let table := observationTerminalTable mode (some input) data
      input.Valid mode ∧ table.Constraints ∧ table.Guarantees ∧
        final mode held.counter input.pc held.enabled = finalFor source.sail target.sail := by
  have dynamic := execution.1.dynamicMatch
  obtain ⟨rows, route, count, bounds, sorted, _⟩ := admissibleExecution_routeObservations execution
  obtain ⟨forMode, routedMode, modes⟩ := admissibleExecution_terminalModes execution data
  obtain rfl := Option.some.inj (route.symm.trans routedMode)
  obtain ⟨forPC, routedPC, _, pc⟩ := admissibleExecution_terminalPC execution
  obtain rfl := Option.some.inj (route.symm.trans routedPC)
  obtain ⟨counter, enabled⟩ := held_counter (p := p) execution.1.1 dynamic rows count
    (history_spec (p := p) source.sail rows (fun r m => (bounds r m).1) (fun r m => (bounds r m).2) sorted)
  obtain ⟨valid, constraints, guarantees⟩ := (modes (Mode.of source.sail target.sail)).mp (mode_accepts execution dynamic)
  refine ⟨rows, route, valid, constraints, guarantees, ?_⟩
  rw [counter, pc, enabled]
  rfl

/-- The complete installed observation subsystem has an honest witness on every admissible
mixed execution. There is one guarded consumer and three physical terminal components. Their
signed state ledger closes against the verifier's actual source and target. The receipt ledger
closes against the 25-family instruction compiler's actual raw successors. -/
theorem admissibleExecution_observationWitness {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (data : ProverData (ZMod p)) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      ObservesOrdinary (policy p image) image.program source.realize events rows ∧
      ∃ height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size,
      let consumer := paddedTable source.sail rows (WitnessGeneration.demandPadding rows.length) data height
      let start := startFor (p := p) source.sail
      let held := (history start rows).2
      let mode := Mode.of source.sail target.sail
      let input := terminalInput held
      let terminals := observationTerminalTables mode input data
      consumer.Constraints ∧ consumer.Guarantees ∧
      (∀ table ∈ terminals, table.Constraints ∧ table.Guarantees) ∧ input.Valid mode ∧
      final mode held.counter input.pc held.enabled = finalFor source.sail target.sail ∧
      LogUpBalanced ((rows.map fun row => InstructionReceipt.channel.pushedValue row.rawPushState.toMessage) ++
        consumer.interactionsWith InstructionReceipt.channel.toRaw) ∧
      LogUpBalanced (([stateChannel.pushedValue start, stateChannel.pulledValue (finalFor source.sail target.sail)] ++
        consumer.interactionsWith stateChannel.toRaw) ++ terminals.flatMap (·.interactionsWith stateChannel.toRaw)) := by
  obtain ⟨rows, route, count, seen, height, constraints, guarantees, receipts, chain⟩ :=
    admissibleExecution_observationTable execution data
  obtain ⟨sameRows, same, valid, _, _, sentinel⟩ := admissibleExecution_observationEndpoint execution data
  obtain rfl := Option.some.inj (route.symm.trans same)
  let start := startFor (p := p) source.sail
  let held := (history start rows).2
  let mode := Mode.of source.sail target.sail
  let input := terminalInput held
  let outgoing := finalFor (p := p) source.sail target.sail
  have edges := observationTerminalTables_ledger mode input data
  change _ = [stateChannel.pulledValue held, stateChannel.pushedValue (final mode held.counter input.pc held.enabled)] at edges
  rw [sentinel] at edges
  refine ⟨rows, route, count, seen, height, constraints, guarantees,
    observationTerminalTables_valid mode input valid data, valid, sentinel, receipts, ?_⟩
  rw [edges]
  exact stateChannel.logUp_append_terminal start held outgoing _ chain

end SP1Clean.TraceGen
