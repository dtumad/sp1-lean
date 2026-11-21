import SP1Clean.Proofs.Completeness.ExecutionObservation

/-! # Closing an ordinary observation chain across host calls

A host-only suffix preserves every register used by the observation terminal. For a segment
consisting entirely of host calls this constructs the actual sentinel link fixed by both
supplied snapshots, also when the incoming nextPC is absent or exceeds the three bus limbs.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target OrdinaryObservation
open LeanRV64D (Register)

private theorem host_only_register {host : HostPolicy} {program : GuestProgram} {s t : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath host program s events t)
    (hostOnly : events.countP ExecutionEvent.isOrdinary = 0)
    (reg : Register) (notPc : reg ≠ .PC) (notX5 : reg ≠ .x5) :
    t.sail.regs.get? reg = s.sail.regs.get? reg := by
  induction path with
  | nil => rfl
  | @cons source middle last event later step _ ih =>
    cases step with
    | ordinary => simp [List.countP_cons] at hostOnly
    | syscall ran =>
      obtain ⟨pc, exec, _, _, _, _, targetEq, _⟩ := HostState.step_observations ran
      exact (ih (by simpa [List.countP_cons] using hostOnly)).trans
        (targetEq ▸ exec.other_register_frame source.sail pc reg notPc notX5)

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
  have frame := host_only_register execution.1.2 hostOnly
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

/-- The selected terminal has one physical row; the other modes have no demand. -/
def observationTerminalTable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (mode : Mode)
    (input : TerminalInputs (ZMod p)) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let component := terminalComponent (p := p) mode
  let rows := [input]
  Table.build component rows (component.inputData rows data) (ProverHint.empty _)
    (by exact Nat.le_of_lt (by decide : 1 < UInt64.size)) (by trivial) (component.inputData_consistent rows data)

/-- A valid last observation constructs the installed terminal component's physical witness. -/
theorem observationTerminalTable_valid {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] {mode : Mode}
    (input : TerminalInputs (ZMod p)) (valid : input.Valid mode) (data : ProverData (ZMod p)) :
    (observationTerminalTable mode input data).Constraints ∧ (observationTerminalTable mode input data).Guarantees := by
  let component := terminalComponent (p := p) mode
  have assumptions (row : component.Input (ZMod p)) (member : row ∈ [input]) :
      component.circuit.ProverAssumptions row (component.inputData [input] data) (ProverHint.empty _) := by
    obtain rfl := List.mem_singleton.mp member
    cases mode <;> exact valid
  unfold observationTerminalTable
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ assumptions, Table.build_guarantees _ _ _ _ _ _ _ assumptions⟩

/-- Clean builds a valid physical terminal at the mode selected by the actual snapshots. -/
theorem admissibleExecution_hostOnlyTerminalTable {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    (hostOnly : events.countP ExecutionEvent.isOrdinary = 0) (data : ProverData (ZMod p)) :
    let mode := Mode.of source.sail target.sail
    let input := terminalInput (startFor (p := p) source.sail)
    let table := observationTerminalTable mode input data
    table.Constraints ∧ table.Guarantees ∧ final mode input.previous.counter input.pc input.previous.enabled =
      finalFor source.sail target.sail := by
  obtain ⟨_, _, valid, terminal⟩ := admissibleExecution_hostOnlyTerminal execution hostOnly
  obtain ⟨constraints, guarantees⟩ := observationTerminalTable_valid _ valid data
  exact ⟨constraints, guarantees, terminal⟩

end SP1Clean.TraceGen
