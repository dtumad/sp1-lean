import SP1Clean.Proofs.Completeness.ExecutionObservation

/-! # Closing an ordinary observation chain across host calls

A host-only suffix preserves every register used by the observation terminal. For a segment
consisting entirely of host calls this constructs the actual sentinel link fixed by both
supplied snapshots, also when the incoming nextPC is absent or exceeds the three bus limbs.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target OrdinaryObservation
open LeanRV64D (Register)

private theorem terminalInput_start {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] {s : SailSnapshot} :
    (terminalInput (startFor (p := p) s)).carryLow = 0 ∧
      (terminalInput (startFor (p := p) s)).carryMiddle = 0 ∧
      (terminalInput (startFor (p := p) s)).pc = (startFor (p := p) s).pc := by
  let pc := (s.registers.get? Register.nextPC : Option (BitVec 64)).getD 0
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have low : ((startFor (p := p) s).pc[0]).val < 65536 := isU64_bitVecToWord pc 0
  have middle : ((startFor (p := p) s).pc[1]).val < 65536 := isU64_bitVecToWord pc 1
  have a : (terminalInput (startFor (p := p) s)).carryLow = 0 := by
    simp only [terminalInput, Nat.div_eq_of_lt low, Nat.cast_zero]
  have b : (terminalInput (startFor (p := p) s)).carryMiddle = 0 := by
    simp only [terminalInput, Nat.div_eq_of_lt low, Nat.add_zero, Nat.div_eq_of_lt middle, Nat.cast_zero]
  refine ⟨a, b, ?_⟩
  simp only [TerminalInputs.pc, a, b, zero_mul, sub_zero, add_zero]
  exact Vector.ext fun i hi => by interval_cases i <;> rfl

/-- A host-only semantic segment constructs its actual terminal input, including the case of
zero events. Its normalized output is the exact outgoing sentinel selected by the two snapshots.
Neither clock-mode selection nor nextPC/retirement agreement is a caller input. -/
theorem admissibleExecution_hostOnlyTerminal {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    (hostOnly : events.countP ExecutionEvent.isOrdinary = 0) :
    routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some [] ∧
    quiet source.sail target.sail = true ∧
    let held := (history (startFor (p := p) source.sail) []).2
    let mode := Mode.of source.sail target.sail
    let input := terminalInput held
    input.Valid mode ∧ final mode held.counter input.pc held.enabled = finalFor source.sail target.sail := by
  have frame := execution.1.2.register_of_host_only hostOnly
  have quietRows := (quiet_iff source.sail target.sail).mpr
    ⟨frame .minstret_increment (by decide) (by decide), frame .mip (by decide) (by decide),
      frame .written_event_index (by decide) (by decide), frame .nextPC (by decide) (by decide)⟩
  have counter : target.sail.registers.get? Register.minstret = source.sail.registers.get? Register.minstret :=
    frame .minstret (by decide) (by decide)
  have next : target.sail.registers.get? Register.nextPC = source.sail.registers.get? Register.nextPC :=
    frame .nextPC (by decide) (by decide)
  obtain ⟨rows, routed, count, _⟩ := admissibleExecution_routeObservations execution
  obtain rfl := List.length_eq_zero_iff.mp (count.trans hostOnly)
  let start := startFor (p := p) source.sail
  obtain ⟨lo, mid, same⟩ := terminalInput_start (p := p) (s := source.sail)
  have clock : TerminalSpec (Mode.of source.sail target.sail) start := by
    have h := history_terminal (p := p) source.sail [] (Mode.of source.sail target.sail) (by simp) (by simp)
    apply h.mpr
    unfold Mode.of
    rw [quietRows]
    cases refreshed source.sail target.sail <;> trivial
  refine ⟨routed, quietRows, ⟨Or.inl lo, Or.inl mid, clock⟩, ?_⟩
  change final _ start.counter (terminalInput start).pc start.enabled = _
  rw [show (terminalInput start).pc = start.pc from same]
  simp only [start, startFor, finalFor, OrdinaryObservation.start, counter, next]

open Circuit Air.Flat
open Soundness.OrdinaryObservation (terminalComponent)

/-- A selected terminal gets one row; an unselected mode gets an empty physical table. -/
def observationTerminalTable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (mode : Mode)
    (entry : Option (TerminalInputs (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let component := terminalComponent (p := p) mode
  let rows := entry.toList
  Table.build component rows (component.inputData rows data) (ProverHint.empty _)
    (by cases entry with
      | none => exact Nat.zero_le _
      | some => exact (by decide : 1 ≤ UInt64.size)) (by trivial) (component.inputData_consistent rows data)

/-- Validating the optional input constructs the terminal's constraints and channel guarantees. -/
theorem observationTerminalTable_valid {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] {mode : Mode}
    (entry : Option (TerminalInputs (ZMod p))) (valid : ∀ input ∈ entry, input.Valid mode) (data : ProverData (ZMod p)) :
    (observationTerminalTable mode entry data).Constraints ∧ (observationTerminalTable mode entry data).Guarantees := by
  let component := terminalComponent (p := p) mode
  have assumptions (row : component.Input (ZMod p)) (member : row ∈ entry.toList) :
      component.circuit.ProverAssumptions row (component.inputData entry.toList data) (ProverHint.empty _) := by
    have accepted := valid row (by
      cases entry with
      | none => exact nomatch member
      | some input => exact congrArg some (List.mem_singleton.mp member).symm)
    cases mode <;> exact accepted
  unfold observationTerminalTable
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ assumptions, Table.build_guarantees _ _ _ _ _ _ _ assumptions⟩

/-- Reading the state ledger of an honest terminal decodes its exact optional input. -/
theorem observationTerminalTable_ledger {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (mode : Mode)
    (entry : Option (TerminalInputs (ZMod p))) (data : ProverData (ZMod p)) :
    (observationTerminalTable mode entry data).interactionsWith stateChannel.toRaw =
      entry.toList.flatMap (fun input => [stateChannel.pulledValue input.previous,
        stateChannel.pushedValue (final mode input.previous.counter input.pc input.previous.enabled)]) := by
  rw [Soundness.OrdinaryObservation.terminal_state_ledger _ mode rfl]
  suffices decoded : Soundness.OrdinaryObservation.terminalRows (observationTerminalTable mode entry data) = entry.toList by
    rw [decoded]
    rfl
  cases entry with
  | none => rfl
  | some input =>
    let c := terminalComponent (p := p) mode
    let prepared := c.inputData [input] data
    exact congrArg (fun x => [x]) (c.rowInput_buildRow input prepared prepared (ProverHint.empty _))

/-- All three installed terminal components, in their physical order. -/
def observationTerminalTables {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    (selected : Mode) (input : TerminalInputs (ZMod p)) (data : ProverData (ZMod p)) : List (Table (ZMod p)) :=
  ([.empty, .nonempty, .any] : List Mode).map fun mode =>
    observationTerminalTable mode (if mode = selected then some input else none) data

/-- The selected row supplies exactly one transition across the full three-table inventory. -/
theorem observationTerminalTables_ledger {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (selected : Mode)
    (input : TerminalInputs (ZMod p)) (data : ProverData (ZMod p)) :
    (observationTerminalTables selected input data).flatMap (·.interactionsWith stateChannel.toRaw) =
      [stateChannel.pulledValue input.previous,
       stateChannel.pushedValue (final selected input.previous.counter input.pc input.previous.enabled)] := by
  cases selected <;> simp [observationTerminalTables, observationTerminalTable_ledger]

/-- The selected input's validity constructs the local witness in every terminal slot. -/
theorem observationTerminalTables_valid {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (selected : Mode)
    (input : TerminalInputs (ZMod p)) (valid : input.Valid selected) (data : ProverData (ZMod p)) :
    ∀ table ∈ observationTerminalTables selected input data, table.Constraints ∧ table.Guarantees := by
  intro table listed
  obtain ⟨mode, _, rfl⟩ := List.mem_map.mp listed
  apply observationTerminalTable_valid
  intro row member
  split at member
  · rename_i same
    obtain rfl := Option.some_inj.mp member
    exact same ▸ valid
  · exact nomatch member

/-- Clean builds a valid physical terminal at the mode selected by the actual snapshots. -/
theorem admissibleExecution_hostOnlyTerminalTable {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    (hostOnly : events.countP ExecutionEvent.isOrdinary = 0) (data : ProverData (ZMod p)) :
    let mode := Mode.of source.sail target.sail
    let input := terminalInput (startFor (p := p) source.sail)
    let table := observationTerminalTable mode (some input) data
    table.Constraints ∧ table.Guarantees ∧ final mode input.previous.counter input.pc input.previous.enabled =
      finalFor source.sail target.sail := by
  obtain ⟨_, _, valid, terminal⟩ := admissibleExecution_hostOnlyTerminal execution hostOnly
  obtain ⟨constraints, guarantees⟩ := observationTerminalTable_valid (some _) (by simpa using valid) data
  exact ⟨constraints, guarantees, terminal⟩

private theorem receipt_pc_bounds {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (row : RoutedEvent) :
    let msg := row.rawPushState.toMessage (p := p)
    msg.pc0.val < 2 * 65536 ∧ msg.pc1.val < 65536 ∧ msg.pc2.val < 65536 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  suffices natural : row.rawPushState.pc0 < 2 * 65536 ∧ row.rawPushState.pc1 < 65536 ∧ row.rawPushState.pc2 < 65536 by
    dsimp only [StateRecord.toMessage]
    rw [ZMod.val_natCast_of_lt (by omega : row.rawPushState.pc0 < p),
      ZMod.val_natCast_of_lt (by omega : row.rawPushState.pc1 < p),
      ZMod.val_natCast_of_lt (by omega : row.rawPushState.pc2 < p)]
    exact natural
  have straight (n : ℕ) : n % 2 ^ 16 + 4 < 2 * 65536 ∧ n / 2 ^ 16 % 2 ^ 16 < 65536 ∧
      n / 2 ^ 32 % 2 ^ 16 < 65536 := by omega
  have control (n : ℕ) : n % 2 ^ 16 < 2 * 65536 ∧ n / 2 ^ 16 % 2 ^ 16 < 65536 ∧
      n / 2 ^ 32 % 2 ^ 16 < 65536 := by omega
  rcases row with ⟨id, event⟩
  cases id <;> first | exact straight _ | exact control _


/-- The chronological history retains the last unnormalized successor limbs exactly. -/
theorem history_last_pc {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (initial : State (ZMod p))
    (earlier : List RoutedEvent) (last : RoutedEvent) :
    (history initial (earlier ++ [last])).2.pc =
      #v[(last.rawPushState.toMessage (p := p)).pc0, last.rawPushState.toMessage.pc1, last.rawPushState.toMessage.pc2] := by
  rw [history_append]
  rfl

/-- Every generated held PC fits the terminal carry normalizer, including a straight-line
successor with a carry from the low limb. -/
theorem observationHistory_pc_bounds {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    (source : SailSnapshot) (rows : List RoutedEvent) :
    let held := (history (startFor (p := p) source) rows).2
    held.pc[0].val < 2 * 65536 ∧ held.pc[1].val < 65536 ∧ held.pc[2].val < 65536 := by
  induction rows using List.reverseRecOn with
  | nil =>
    let pc := (source.registers.get? Register.nextPC : Option (BitVec 64)).getD 0
    have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
    have digit := isU64_bitVecToWord (p := p) pc
    exact ⟨(digit 0).trans (by decide), digit 1, digit 2⟩
  | append_singleton earlier last _ =>
    dsimp only
    rw [history_last_pc]
    exact receipt_pc_bounds last


/-- The honest physical terminal input is valid exactly in the modes accepting this tape's
ordinary count. In every such mode it constructs a table satisfying the installed constraints
and guarantees. Its mode is subsequently selected by the public snapshots. -/
theorem admissibleExecution_terminalModes {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (data : ProverData (ZMod p)) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      ∀ mode,
        let input := terminalInput (history (startFor (p := p) source.sail) rows).2
        let table := observationTerminalTable mode (some input) data
        mode.AcceptsCount (events.countP ExecutionEvent.isOrdinary) ↔ input.Valid mode ∧ table.Constraints ∧ table.Guarantees := by
  obtain ⟨rows, routed, count, bounds, _⟩ := admissibleExecution_routeObservations execution
  refine ⟨rows, routed, ?_⟩
  intro mode
  have clock := history_terminal (p := p) source.sail rows mode (fun row member => (bounds row member).1)
    (fun row member => (bounds row member).2)
  obtain ⟨low, middle, _⟩ := observationHistory_pc_bounds (p := p) source.sail rows
  cases mode <;> simp only [Mode.AcceptsCount, ← count, ne_eq, List.length_eq_zero_iff] at clock ⊢
  all_goals
    constructor
    · intro allowed
      have valid := (Soundness.OrdinaryObservation.terminalInput_canonical (clock.mpr allowed) low middle).1
      exact ⟨valid, observationTerminalTable_valid (some _) (by simpa using valid) data⟩
    · rintro ⟨valid, _⟩
      exact clock.mp valid.2.2

end SP1Clean.TraceGen
