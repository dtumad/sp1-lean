import SP1Clean.Soundness.LocalCoreGrounding
import SP1Clean.Soundness.CoreExecutionEvents
import SP1Clean.Model.Core.ExecutionReplay

/-! # Stateful replay of the local AIR's ordered events

The carrier determines one event tape. Replay starts at the full checked source and threads the
actual host state, validating every claimed syscall against concrete host execution. Its Sail
projection is the trajectory used by grounding. Success is not assumed here: a forged host result
may make replay fail even when the current AIR accepts it. Successful replay has the exact derived
clock at every covered position; the extension past the tape contributes no semantic steps.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow ordered_at_of_alignment)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Every active occurrence is retained in the balance-derived order. -/
noncomputable def GroundingCarrier.events {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    List Machine.ExecutionEvent := carrier.ordered.map ExecutionRow.event

theorem GroundingCarrier.events_length {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness) :
    carrier.events.length = carrier.rows.length := by
  simpa only [events, List.length_map] using carrier.aligned.length_eq.symm

/-- The actual event occurrence is identified by its natural State clock. -/
theorem GroundingCarrier.ordered_at {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.ordered[n]? = some event := by
  apply ordered_at_of_alignment (p := p) (ExecutionRow.facts witness.data)
    (incoming := initialBoundaryStateMessage witness.publicInput)
    (outgoing := finalBoundaryStateMessage witness.publicInput)
    (ordered := carrier.ordered) (rows := carrier.rows) (event := event) (n := n)
    carrier.aligned carrier.stateWalk (fun row member => (carrier.rowOK row member).timeGap)
    (carrier.exhaustive.mem_iff.mpr member)
  exact atIndex

theorem GroundingCarrier.event_at {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.events[n]? = some event.event := by
  simp only [events, List.getElem?_map, carrier.ordered_at member atIndex, Option.map_some]

/-- The full source, including its actual host queues and exit status, initializes replay. -/
noncomputable def GroundingCarrier.pairedTrajectory {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) : ℕ → Option ExecutionState :=
  executionTrajectory policy (image.toGuestProgram valid) source.realize carrier.events

/-- Grounding observes the Sail projection of that same evolving whole state. -/
noncomputable def GroundingCarrier.trajectory {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) : Trajectory :=
  fun n => (carrier.pairedTrajectory valid policy n).map ExecutionState.sail

theorem GroundingCarrier.pairedTrajectory_zero {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) :
    carrier.pairedTrajectory valid policy 0 = some source.realize := rfl

theorem GroundingCarrier.trajectory_zero {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) :
    carrier.trajectory valid policy 0 = some source.sail.realize := rfl

/-- No handler reset or row-chosen result occurs between events. -/
theorem GroundingCarrier.pairedTrajectory_succ {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.pairedTrajectory valid policy (n + 1) =
      (carrier.pairedTrajectory valid policy n).bind
        (fun state => replayStep? policy (image.toGuestProgram valid) state event.event) :=
  executionTrajectory_succ _ _ _ _ (carrier.event_at member atIndex)

/-- Original physical State successors occur at the next timeline position. -/
theorem GroundingCarrier.originalTimeStep {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ∀ n, StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n →
      StateMsg.timeNat (event.facts witness.data).statePush = carrier.timeline.start (n + 1) := by
  have originalMem := List.mem_map_of_mem (f := ExecutionRow.facts witness.data)
    (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨row, rowMem, aligned⟩ := forall₂_exists_right carrier.aligned.flip _ originalMem
  intro n time
  rw [← aligned.pushTime]
  exact carrier.timeStep row rowMem n (aligned.pullTime.trans time)

private theorem event_durations {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    carrier.rows.map rowDuration = carrier.events.map Machine.ExecutionEvent.duration := by
  rw [GroundingCarrier.events, List.map_map]
  apply List.ext_getElem
  · simpa only [List.length_map] using carrier.aligned.length_eq
  · intro n left right
    have leftBound : n < carrier.rows.length := by simpa only [List.length_map] using left
    have rightBound : n < carrier.ordered.length := by simpa only [List.length_map] using right
    have aligned := carrier.aligned.get leftBound (by simpa only [List.length_map] using rightBound)
    simp only [List.get_eq_getElem, List.getElem_map, Function.comp_apply] at aligned ⊢
    have duration := (executionRows_advancing witness constraints balanced
      (carrier.exhaustive.mem_iff.mp (List.getElem_mem rightBound))).2
    rw [ExecutionRow.edge_eq_facts] at duration
    dsimp only at duration
    rw [rowDuration, aligned.pushTime, aligned.pullTime, duration, Nat.add_sub_cancel_left,
      ExecutionRow.event_duration]

/-- The AIR timeline counts semantic event widths, without counting providers or inactive rows. -/
theorem GroundingCarrier.timeline_events {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (n : ℕ) (covered : n ≤ carrier.events.length) :
    carrier.timeline.start n = source.clock + ((carrier.events.take n).map Machine.ExecutionEvent.duration).sum := by
  rw [timeline, NativeCore.ExecutionCarrier.timeline, rowTimeline, Timeline.ofDurations_start_le _ _ _ (by
    simpa only [List.length_map, carrier.events_length] using covered),
    event_durations carrier constraints balanced, ← List.map_take]
  exact congrArg (fun clock => clock + ((carrier.events.take n).map Machine.ExecutionEvent.duration).sum)
    (source_state_encoding witness constraints balanced).1

/-- A successful paired prefix carries exactly the clock selected by the AIR walk. -/
theorem GroundingCarrier.pairedTrajectory_clock {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {n : ℕ} (covered : n ≤ carrier.events.length) {state : ExecutionState}
    (present : carrier.pairedTrajectory valid policy n = some state) :
    state.clock = carrier.timeline.start n := by
  rw [carrier.timeline_events constraints balanced n covered]
  exact replayEvents?_clock present

/-- A nonempty local AIR segment must start at a running host. -/
theorem source_running_of_event {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) : source.host.exitCode = none := by
  by_contra stopped
  rw [executionRows_nil_of_stopped witness constraints balanced stopped] at member
  exact List.not_mem_nil member

/-- At a replayed prefix with an authenticated code fetch, terminal status is impossible.
The claim uses the actual evolving host, not an assumed host-invariance property. -/
theorem GroundingCarrier.pairedTrajectory_running_of_fetch {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {event : ExecutionRow p} (member : event ∈ executionRows witness)
    {n : ℕ} {state : ExecutionState} (present : carrier.pairedTrajectory valid policy n = some state)
    {pc : BitVec 64} {word : BitVec 32}
    (atPc : state.sail.regs.get? LeanRV64D.Defs.Register.PC = some pc)
    (fetched : (image.toGuestProgram valid).fetchWord pc = some word) : state.host.exitCode = none := by
  exact replayEvents?_running_of_fetch (source_running_of_event witness constraints balanced member) present atPc fetched

/-- Final State truth recovers successful replay of the entire tape and its complete returned
state. Only PC/clock are bound to public fields here; full outgoing snapshot agreement is separate. -/
theorem GroundingCarrier.replay_of_finalTruth {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (final : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
      (finalBoundaryStateMessage witness.publicInput)) :
    ∃ target, replayEvents? policy (image.toGuestProgram valid) source.realize carrier.events = some target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) := by
  obtain ⟨n, state, present, time, pc, _, _⟩ := final
  have atEnd : n = carrier.rows.length := start_injective carrier.timeline (time.symm.trans carrier.finalClock.symm)
  change (carrier.pairedTrajectory valid policy n).map ExecutionState.sail = some state at present
  rw [atEnd, ← carrier.events_length] at present
  obtain ⟨target, paired, sail⟩ := Option.map_eq_some_iff.mp present
  refine ⟨target, ?_, ?_, ?_⟩
  · simpa only [pairedTrajectory, executionTrajectory, List.take_length] using paired
  · have clock := carrier.pairedTrajectory_clock valid policy constraints balanced le_rfl paired
    rwa [carrier.events_length, carrier.finalClock] at clock
  · rwa [sail]

end SP1Clean.Soundness.LocalCore
