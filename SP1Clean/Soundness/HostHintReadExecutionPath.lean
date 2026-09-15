import SP1Clean.Soundness.HostHintReadExecution

/-! # Local execution soundness for the installed instruction, control, and hint AIR

The constraints and balanced ledger reconstruct one finite path of normally retiring Sail
instructions and concrete host calls from the complete incoming state. Every active event occurs
exactly once, and final PC, clock, and physical Memory-frontier values agree with that path.
Empty segments remain identity paths; inactive padding contributes no execution steps.

This is the installed source-hint assembly's soundness theorem. Complete outgoing snapshot and
Exit-bus binding, WRITE/VERIFY handlers, and constructive completeness remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

private theorem path_of_replay {policy : HostPolicy} {program : Target.GuestProgram}
    {source target : ExecutionState} {events : List Machine.ExecutionEvent}
    (success : replayEvents? policy program source events = some target)
    (sound : ∀ n current next event, events[n]? = some event →
      replayEvents? policy program source (events.take n) = some current →
      replayStep? policy program current event = some next →
        ExecutionStep policy program current event next) :
    ExecutionPath policy program source events target := by
  induction events generalizing source with
  | nil => cases success; exact .nil _
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    refine .cons (sound 0 source middle event rfl rfl step) (ih suffix ?_)
    intro n current next label atLabel prefixReplay replay
    apply sound (n + 1) current next label (by simpa only [List.getElem?_cons_succ] using atLabel) _ replay
    simpa only [List.take_succ_cons, replayEvents?, step, Option.bind_some] using prefixReplay

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance pathLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance pathLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {channels : List (RawChannel (ZMod p))}

private theorem step_of_replay (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (n : ℕ) (current next : ExecutionState) (event : Machine.ExecutionEvent)
    (atEvent : carrier.events[n]? = some event)
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current)
    (replay : replayStep? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current event = some next) :
    ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event next := by
  simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
  obtain ⟨row, atRow, rfl⟩ := Option.map_eq_some_iff.mp atEvent
  have member := carrier.exhaustive.mem_iff.mp (List.mem_of_getElem? atRow)
  cases row with
  | instruction row =>
    have grounded := (carrier.ground valid constraints balanced).1 _ member
    have time := carrier.time_of_ordered_at atRow
    rw [(eventFacts_state_fetch _ _ _).1] at time
    have currency : ∀ mp ∈ (row.ordinaryRowFacts witness.data).memPulls,
        MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
          LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline
            (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
      intro mp mem
      apply grounded.2 mp
      exact List.mem_append_left _ mem
    obtain ⟨target, step⟩ := carrier.instruction_step valid constraints balanced member grounded.1 currency prefixReplay time
    have same : target = next := Option.some.inj (step.replay.symm.trans replay)
    rwa [same] at step
  | syscall row => exact (replayHost?_eq_some_iff _ _ _ _ _).mp replay
  | halt row => exact (replayHost?_eq_some_iff _ _ _ _ _).mp replay

private theorem final_replay (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (truth : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (finalBoundaryStateMessage witness.publicInput)) :
    ∃ target, carrier.pairedTrajectory valid carrier.events.length = some target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) := by
  obtain ⟨n, state, present, time, pc, _, _⟩ := truth
  have atEnd : n = carrier.rows.length := start_injective carrier.timeline (time.symm.trans carrier.finalClock.symm)
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  rw [atEnd, ← carrier.events_length] at present
  obtain ⟨target, paired, sail⟩ := Option.map_eq_some_iff.mp present
  refine ⟨target, paired, ?_, ?_⟩
  · have clock := replayEvents?_clock paired
    rw [List.take_length] at clock
    have timeline := congrArg (fun tl : Timeline => tl.start carrier.events.length)
      (carrier.timeline_events constraints balanced)
    rw [eventTimeline_start_le _ _ _ le_rfl, List.take_length, carrier.events_length, carrier.finalClock] at timeline
    exact clock.trans timeline.symm
  · rwa [sail]

/-- Raw installed AIR constraints and balance yield a normally retiring local execution on the
derived complete event tape. Its endpoint agrees with the public PC/clock and every final record. -/
theorem GroundingCarrier.execution (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ target, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize carrier.events target ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value) := by
  have grounded := carrier.ground valid constraints balanced
  obtain ⟨target, present, clock, pc⟩ := final_replay valid carrier constraints balanced grounded.2.1
  have replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target := by
    simpa only [GroundingCarrier.pairedTrajectory, ExecutionCarrier.pairedTrajectory,
      executionTrajectory, List.take_length] using present
  refine ⟨target, path_of_replay replay (step_of_replay valid carrier constraints balanced), clock, pc, ?_⟩
  intro loc message finalRecord
  have value := grounded.2.2 loc message finalRecord
  have before : carrier.trajectory valid carrier.events.length = some target.sail := by
    simp only [GroundingCarrier.trajectory, present, Option.map_some]
  rw [← carrier.finalClock, ← carrier.events_length] at value
  exact (localValueAtG_stepStart_iff before).mp value

/-- The installed ensemble proves a local RISC-V/host path without caller-supplied ordering,
grounding, or event semantics. The path exhausts the active physical inventory, preserving repeated
occurrences and erasing inactive padding. Complete outgoing snapshot binding is not asserted. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events target, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      ∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value) := by
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness constraints balanced
  obtain ⟨target, path, endpoint⟩ := carrier.execution valid constraints balanced
  exact ⟨carrier.events, target, path, carrier.exhaustive.map ExecutionRow.event, endpoint⟩

end SP1Clean.Soundness.HostHintReadCPU
