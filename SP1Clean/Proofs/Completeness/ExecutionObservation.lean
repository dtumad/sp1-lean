import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Proofs.Completeness.OrdinaryObservationPadding
import ToClean.Air.DemandPadding

/-! # Compiling the ordinary observation history of an admissible local execution

Replay supplies each complete incoming and outgoing state. The instruction compiler routes
ordinary transitions in tape order; every syscall advances the same replay. This projection
uses the ordinary rows' State receipts and does not produce the mixed Memory ledger.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

/-- Replay the tape once and compile each ordinary transition against its actual source clock.
The running frontier is used only to populate the ordinary instruction rows. -/
noncomputable def routeObservations? (host : HostPolicy) (program : GuestProgram) :
    AccessFrontier → ExecutionState → List ExecutionEvent → Option (List RoutedEvent)
  | _, _, [] => some []
  | frontier, current, event :: later => do
    let next ← replayStep? host program current event
    match event with
    | .syscall _ => routeObservations? host program frontier next later
    | .ordinary =>
      let view ← projectSP1Transition? program ⟨current.sail, ⟨.ordinary, next.sail⟩⟩
      let result ← compileInstructionEvent? view frontier current.clock
      let routed ← routeObservations? host program result.nextFrontier next later
      return result.routed :: routed

/-- Every ordinary tape position has exactly its compiler row at the rank of that position.
Both the clock and the program counter are read from its actual incoming complete state. -/
def ObservesOrdinary (host : HostPolicy) (program : GuestProgram) (current : ExecutionState)
    (events : List ExecutionEvent) (rows : List RoutedEvent) : Prop :=
  ∀ cut, events[cut]? = some .ordinary → ∃ row before pc,
    rows[((events.take cut).countP ExecutionEvent.isOrdinary)]? = some row ∧
    executionTrajectory host program current events cut = some before ∧
    row.clock = before.clock ∧ before.sail.regs.get? LeanRV64D.Register.PC = some pc ∧ row.pc = pc.toNat

private theorem observes_ordinary {host : HostPolicy} {program : GuestProgram}
    {current middle : ExecutionState} {later : List ExecutionEvent} {row : RoutedEvent} {rows : List RoutedEvent}
    (step : ExecutionStep host program current .ordinary middle) (seen : ObservesOrdinary host program middle later rows)
    (time : row.clock = current.clock) {pc : BitVec 64}
    (pcSource : current.sail.regs.get? LeanRV64D.Register.PC = some pc) (pcRow : row.pc = pc.toNat) :
    ObservesOrdinary host program current (.ordinary :: later) (row :: rows) := by
  intro cut idx
  cases cut with
  | zero => exact ⟨row, current, pc, rfl, rfl, time, pcSource, pcRow⟩
  | succ n =>
    obtain ⟨r, s, q, atRow, atCut, facts⟩ := seen n idx
    refine ⟨r, s, q, ?_, ?_, facts⟩
    · simpa [List.countP_cons] using atRow
    · simpa only [executionTrajectory, List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using atCut

private theorem observes_syscall {host : HostPolicy} {program : GuestProgram}
    {current middle : ExecutionState} {call : CoreSyscallEvent} {later : List ExecutionEvent} {rows : List RoutedEvent}
    (step : ExecutionStep host program current (.syscall call) middle) (seen : ObservesOrdinary host program middle later rows) :
    ObservesOrdinary host program current (.syscall call :: later) rows := by
  intro cut idx
  cases cut with
  | zero => simp at idx
  | succ n =>
    obtain ⟨row, s, pc, atRow, atCut, facts⟩ := seen n idx
    refine ⟨row, s, pc, ?_, ?_, facts⟩
    · simpa [List.countP_cons] using atRow
    · simpa only [executionTrajectory, List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using atCut

private theorem route_from {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {current last : ExecutionState} {later : List ExecutionEvent}
    (path : ExecutionPath (policy p image) image.program current later last)
    (before : List ExecutionEvent) (part : events = before ++ later)
    (reached : replayEvents? (policy p image) image.program source.realize before = some current)
    (frontier : AccessFrontier) :
    ∃ rows, routeObservations? (policy p image) image.program frontier current later = some rows ∧
      rows.length = later.countP ExecutionEvent.isOrdinary ∧
      (∀ row ∈ rows, current.clock ≤ row.clock ∧ 0 < row.clock ∧ row.clock < last.clock) ∧
      rows.Pairwise (fun a b => a.clock < b.clock) ∧
      ObservesOrdinary (policy p image) image.program current later rows := by
  induction path generalizing before frontier with
  | nil => exact ⟨[], rfl, rfl, by simp, .nil, by intro cut present; simp at present⟩
  | @cons current middle last event later step tail ih =>
    have present : events[before.length]? = some event := by simp [part]
    have atCut : executionTrajectory (policy p image) image.program source.realize events before.length =
        some current := by simpa [executionTrajectory, part] using reached
    have part' : events = (before ++ [event]) ++ later := by simpa only [List.append_assoc, List.singleton_append] using part
    have reached' : replayEvents? (policy p image) image.program source.realize (before ++ [event]) = some middle := by
      simp only [replayEvents?_append, reached, Option.bind_some, replayEvents?, step.replay]
    have advance := step.clock_lt
    cases event with
    | syscall call =>
      obtain ⟨rows, route, len, bounds, sorted, seen⟩ := ih _ part' reached' frontier
      refine ⟨rows, ?_, by simpa using len, ?_, sorted, observes_syscall step seen⟩
      · simp [routeObservations?, step.replay, route]
      · intro row member
        have b := bounds row member
        exact ⟨advance.le.trans b.1, b.2⟩
    | ordinary =>
      obtain ⟨atState, successor, view, result, sameCut, ran, projected, generated, _⟩ :=
        admissibleExecution_compile_at execution present frontier
      obtain rfl := Option.some.inj (atCut.symm.trans sameCut)
      obtain rfl := Option.some.inj (step.replay.symm.trans ran.replay)
      obtain ⟨rows, route, len, bounds, sorted, seen⟩ := ih _ part' reached' result.nextFrontier
      have time := (compileInstructionEvent?_coordinates generated).1
      have phase := (execution.2.1 _ _ _ present atCut).1
      change _ % 8 = 1 at phase
      have tailClock := tail.clock
      refine ⟨result.routed :: rows, ?_, by simp [List.countP_cons, len], ?_, .cons ?_ sorted, ?_⟩
      · simp [routeObservations?, step.replay, projected, generated, route]
      · intro row member
        rcases List.mem_cons.mp member with rfl | rest
        · rw [time]
          exact ⟨le_rfl, by omega, by omega⟩
        · have b := bounds row rest
          exact ⟨advance.le.trans b.1, b.2⟩
      · intro other member
        exact time ▸ advance.trans_le (bounds other member).1
      · exact observes_ordinary step seen time (projectSP1Transition?_components projected).1
          (compileInstructionEvent?_coordinates generated).2

/-- No compiler input or bounds witness is required at the public entry point. -/
theorem admissibleExecution_routeObservations {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (∀ row ∈ rows, 0 < row.clock ∧ row.clock < 2 ^ 48) ∧
      rows.Pairwise (fun a b => a.clock < b.clock) ∧
      ObservesOrdinary (policy p image) image.program source.realize events rows := by
  obtain ⟨rows, route, length, bounds, sorted, seen⟩ := route_from execution execution.1.2 [] rfl rfl (fun _ => 0)
  refine ⟨rows, route, length, ?_, sorted, seen⟩
  intro row member
  have b := bounds row member
  exact ⟨b.2.1, b.2.2.trans execution.2.2.2.2.2.1⟩

open Circuit Air.Flat OrdinaryObservation

/-- The actual mixed tape constructs a locally valid guarded observation table at Clean's demand
height and balances its two signed ledgers. Its physical height follows from the semantic clock
budget. Every active row has the clock and PC of the corresponding replayed ordinary step. -/
theorem admissibleExecution_observationTable {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (data : ProverData (ZMod p)) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      ObservesOrdinary (policy p image) image.program source.realize events rows ∧
      ∃ height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size,
      let table := paddedTable source.sail rows (WitnessGeneration.demandPadding rows.length) data height
      let start := startFor (p := p) source.sail
      let held := (history start rows).2
      table.Constraints ∧ table.Guarantees ∧
      LogUpBalanced ((rows.map fun row => InstructionReceipt.channel.pushedValue row.rawPushState.toMessage) ++
        table.interactionsWith InstructionReceipt.channel.toRaw) ∧
      LogUpBalanced ([stateChannel.pushedValue start, stateChannel.pulledValue held] ++
        table.interactionsWith stateChannel.toRaw) := by
  obtain ⟨rows, route, count, bounds, sorted, seen⟩ := admissibleExecution_routeObservations execution
  have generalBound := WitnessGeneration.demandHeight_bounds rows.length
  have paddedHeight := WitnessGeneration.add_demandPadding rows.length
  have ordinaryBound : rows.length ≤ events.length := count.trans_le List.countP_le_length
  have ticks := event_count_le_ticks events
  have clock := execution.1.2.clock
  change target.clock = source.clock + _ at clock
  have final : target.clock < 2 ^ 48 := execution.2.2.2.2.2.1
  have height : rows.length + WitnessGeneration.demandPadding rows.length ≤ UInt64.size := by
    change _ ≤ 2 ^ 64
    omega
  obtain ⟨constraints, guarantees⟩ := paddedTable_valid source.sail rows (WitnessGeneration.demandPadding rows.length)
    data height (fun row member => (bounds row member).1) (fun row member => (bounds row member).2) sorted
  exact ⟨rows, route, count, seen, height, constraints, guarantees,
    paddedTable_logUp source.sail rows (WitnessGeneration.demandPadding rows.length) data height⟩

end SP1Clean.TraceGen
