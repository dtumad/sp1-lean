import SP1Clean.Proofs.Completeness.ExecutionObservationTerminal
import SP1Clean.FormalModel.ShardNextPC
import SP1Clean.Proofs.Completeness.InstructionSuccessor

/-! # Matching the last routed receipt to the semantic successor -/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target LeanRV64D

private theorem final_ordinary {events : List ExecutionEvent} (active : events.countP ExecutionEvent.isOrdinary ≠ 0) :
    ∃ before later, events = before ++ .ordinary :: later ∧ later.countP ExecutionEvent.isOrdinary = 0 := by
  induction events using List.reverseRecOn with
  | nil => simp at active
  | append_singleton prior event ih =>
    cases event with
    | ordinary => exact ⟨prior, [], rfl, rfl⟩
    | syscall call =>
      obtain ⟨before, later, split, empty⟩ := ih (by simpa [List.countP_append, List.countP_cons] using active)
      exact ⟨before, later ++ [.syscall call], by simp [split], by simp [List.countP_append, empty]⟩

/-- Each generated raw successor receipt denotes the PC and nextPC of the very next complete
Sail state. Bounds come from the selected execution edge, including interior jumps. -/
theorem routed_successor_at {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) {rows : List RoutedEvent}
    (routed : routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows)
    {cut : ℕ} (atEvent : events[cut]? = some .ordinary) :
    ∃ row next, rows[((events.take cut).countP ExecutionEvent.isOrdinary)]? = some row ∧
      executionTrajectory (policy p image) image.program source.realize events (cut + 1) = some next ∧
      next.sail.regs.get? Register.PC = some (StateMsg.pcBits (row.rawPushState.toMessage (p := p))) ∧
      next.sail.regs.get? Register.nextPC = some (StateMsg.pcBits (row.rawPushState.toMessage (p := p))) := by
  obtain ⟨current, next, view, row, _, atCut, ran, projected, made, atRow⟩ := routeObservations?_at routed atEvent
  have nextCut : executionTrajectory (policy p image) image.program source.realize events (cut + 1) = some next := by
    rw [executionTrajectory_succ _ _ _ _ atEvent, atCut, Option.bind_some, ran]
  obtain ⟨s, t, same, step⟩ := execution.1.2.step_at atEvent
  obtain rfl := Option.some.inj (atCut.symm.trans same)
  obtain rfl := Option.some.inj (ran.symm.trans step.replay)
  have frame := execution.1.frame_prefix atCut
  refine ⟨row.routed, next, atRow, nextCut, ?_⟩
  cases step with
  | ordinary _ _ normal permitted =>
    have pc := compileInstructionEvent?_successor (p := p) frame.1 frame.2.1 permitted normal projected made
      (fun _ address => Executes.pc_at execution nextCut address)
    exact ⟨pc, (Advance.ordinary_normal_bookkeeping frame.1 frame.2.1 permitted normal).1.trans pc⟩

private theorem last_pc {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) {earlier : List RoutedEvent}
    {last : RoutedEvent}
    (routed : routeObservations? (policy p image) image.program (fun _ => 0) source.realize events =
      some (earlier ++ [last]))
    (count : (earlier ++ [last]).length = events.countP ExecutionEvent.isOrdinary) :
    target.sail.registers.get? Register.nextPC = some (StateMsg.pcBits (last.rawPushState.toMessage (p := p))) := by
  have active : events.countP ExecutionEvent.isOrdinary ≠ 0 := by simp [← count]
  obtain ⟨before, later, split, empty⟩ := final_ordinary active
  have position : events[before.length]? = some .ordinary := by simp [split]
  have rank : (events.take before.length).countP ExecutionEvent.isOrdinary = earlier.length := by
    simp only [split, List.length_append, List.length_cons, List.length_nil, List.countP_append,
      List.countP_cons, ExecutionEvent.isOrdinary_ordinary, empty, ↓reduceIte] at count
    simpa [split] using (by omega : before.countP ExecutionEvent.isOrdinary = earlier.length)
  obtain ⟨row, next, listed, reached, _, held⟩ := routed_successor_at execution routed position
  rw [rank] at listed
  obtain rfl : row = last := by simpa using listed.symm
  obtain ⟨middle, same, _, tail⟩ := execution.1.2.replay_split (before.length + 1)
  obtain rfl := Option.some.inj (reached.symm.trans same)
  have laterPath : ExecutionPath (policy p image) image.program next later target.realize := by
    simpa [split, List.drop_append_of_le_length] using tail
  exact (laterPath.register_of_host_only empty .nextPC (by decide) (by decide)).trans held

open OrdinaryObservation

/-- The chronological receipt fold recovers the full optional target nextPC, while the
constructed terminal recovers its three normalized limbs. This includes every instruction
family, arbitrary trailing host calls, and an empty or host-only segment. -/
theorem admissibleExecution_terminalPC {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) :
    ∃ rows, routeObservations? (policy p image) image.program (fun _ => 0) source.realize events = some rows ∧
      target.sail.registers.get? Register.nextPC = rows.foldl (fun _ row =>
        some (StateMsg.pcBits (row.rawPushState.toMessage (p := p)))) (source.sail.registers.get? Register.nextPC) ∧
      (terminalInput (history (startFor (p := p) source.sail) rows).2).pc = (finalFor (p := p) source.sail target.sail).pc := by
  obtain ⟨rows, routed, count, bounds, _⟩ := admissibleExecution_routeObservations execution
  refine ⟨rows, routed, ?_⟩
  induction rows using List.reverseRecOn with
  | nil =>
    have empty : events.countP ExecutionEvent.isOrdinary = 0 := count.symm
    obtain ⟨_, quiet, _, terminal⟩ := admissibleExecution_hostOnlyTerminal execution empty
    exact ⟨((quiet_iff _ _).mp quiet).2.2.2, congrArg State.pc terminal⟩
  | append_singleton earlier last _ =>
    have actual := last_pc execution routed count
    have nonempty : events.countP ExecutionEvent.isOrdinary ≠ 0 := by simp [← count]
    obtain ⟨pc, atPC, bounded⟩ := Executes.nextPC_bounded execution nonempty
    obtain rfl := Option.some.inj (atPC.symm.trans actual)
    let held := (history (startFor (p := p) source.sail) (earlier ++ [last])).2
    let msg := last.rawPushState.toMessage (p := p)
    have heldPC : held.pc = #v[msg.pc0, msg.pc1, msg.pc2] := by
      exact history_last_pc _ _ _
    have clock : TerminalSpec .any held := (history_terminal source.sail _ .any
      (fun row member => (bounds row member).1) (fun row member => (bounds row member).2)).mpr trivial
    obtain ⟨lo, mi, hi⟩ := observationHistory_pc_bounds (p := p) source.sail (earlier ++ [last])
    have normalized := Soundness.OrdinaryObservation.terminalInput_pcLimbs clock lo mi hi bounded (by rw [heldPC]; rfl)
    refine ⟨by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using actual, ?_⟩
    simpa only [finalFor, final, actual, Option.getD_some] using normalized.2

end SP1Clean.TraceGen
