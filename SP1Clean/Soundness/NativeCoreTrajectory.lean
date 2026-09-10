import SP1Clean.Soundness.NativeCoreInstructionExecution

/-! # Executing the native AIR's ordered events

The carrier supplies a complete ordered transcript, including ordinary instructions, HALT, and
host calls. The existing event executor determines its trajectory from the checked initial state.
The State walk identifies each event's exact list position, so ordinary successor equations are
conclusions rather than caller premises. The HALT wrapper fixes the zero-code host behavior;
agreement of other host effects with the AIR remains a separate obligation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Decode the actual HALT register words, retaining the raw code until constraints prove it zero. -/
noncomputable def haltEventOfRow (row : HaltChip.Inputs (ZMod p)) : Machine.CoreSyscallEvent where
  clock := StateMsg.timeNat (HaltChip.statePulledMessage row)
  pc := StateMsg.pcBits (HaltChip.statePulledMessage row)
  nextPc := Machine.haltPc
  rawCode := Word.toBitVec64 row.x5_memory.prev_value
  arg1 := Word.toBitVec64 row.x10_memory.prev_value
  arg2 := Word.toBitVec64 row.x11_memory.prev_value
  result := Word.toBitVec64 row.x5_memory.prev_value

/-- The semantic event carried by a physical active row. -/
noncomputable def ExecutionRow.event : ExecutionRow p → Machine.ExecutionEvent
  | .instruction _ => .ordinary
  | .halt row => .syscall (haltEventOfRow row)
  | .syscall row => .syscall (syscallEventOfRow row)

/-- The transcript retains every active row occurrence in the balance-derived State order. -/
noncomputable def GroundingCarrier.events {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness) :
    List Machine.ExecutionEvent :=
  carrier.ordered.map ExecutionRow.event

/-- Execute the carrier's transcript with canonical HALT and the supplied non-HALT host. -/
noncomputable def GroundingCarrier.trajectory {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) : Trajectory :=
  eventTrajectory handler.withHalt (image.toGuestProgram valid) carrier.events image.initialSailState

/-- Execution starts at the checked program image's configured Sail state. -/
theorem GroundingCarrier.trajectory_zero {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) :
    carrier.trajectory valid handler 0 = some image.initialSailState := rfl

/-- A physical event's bus clock identifies its exact position, including repeated row values. -/
theorem GroundingCarrier.ordered_at {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.ordered[n]? = some event := by
  obtain ⟨k, present⟩ := List.mem_iff_getElem?.mp (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨bound, element⟩ := List.getElem?_eq_some_iff.mp present
  have leftBound : k < carrier.rows.length := by
    have lengths := carrier.aligned.length_eq
    simp only [List.length_map] at lengths
    omega
  have related := carrier.aligned.get leftBound (by simpa only [List.length_map] using bound)
  simp only [List.get_eq_getElem, List.getElem_map, element] at related
  have pull := rowTimeline_pullTime_of_getElem? carrier.stateWalk
    (fun row rowMem => (carrier.rowOK row rowMem).timeGap) (List.getElem?_eq_getElem leftBound)
  have same : n = k := (start_injective carrier.timeline)
    (atIndex.symm.trans (related.pullTime.symm.trans pull))
  rwa [same]

/-- The semantic transcript and the clock-indexed event are the same occurrence. -/
theorem GroundingCarrier.event_at {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n) :
    carrier.events[n]? = some event.event := by
  simp only [events, List.getElem?_map, carrier.ordered_at member atIndex, Option.map_some]

/-- Each ordinary event executes the official Sail step at its own derived timeline position. -/
theorem GroundingCarrier.trajectory_ordinary {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    carrier.trajectory valid handler (n + 1) =
      (carrier.trajectory valid handler n).bind Machine.stepOnce := by
  unfold trajectory
  rw [eventTrajectory_succ, carrier.event_at member atIndex]
  rfl

/-- A zero-code HALT event parks the PC and preserves every register and memory location. -/
theorem GroundingCarrier.trajectory_halt {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (handler : Machine.ExecutableSyscallHandler) {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) {n : ℕ}
    (atIndex : StateMsg.timeNat (haltRowFacts row).statePull = carrier.timeline.start n)
    (zero : (haltEventOfRow row).rawCode = 0) :
    carrier.trajectory valid handler (n + 1) = (carrier.trajectory valid handler n).map
      (fun state => { state with regs := state.regs.insert LeanRV64D.Defs.Register.PC Machine.haltPc }) := by
  unfold trajectory
  rw [eventTrajectory_succ, carrier.event_at member atIndex]
  simp only [ExecutionRow.event, Machine.executeEvent?,
    Machine.ExecutableSyscallHandler.withHalt_run_zero _ _ _ _ zero, Option.map_eq_bind,
    Function.comp_def]

end SP1Clean.Soundness.NativeCore
