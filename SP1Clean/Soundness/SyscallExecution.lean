import SP1Clean.Soundness.SyscallTrail
import SP1Clean.Soundness.SyscallWiring

/-!
# The mixed walk drives the row-generic execution engine

`Soundness/LocalExecution.lean` holds the engine: row-generic, trajectory-*consuming*, and — because
it sits below this whole campaign in the import order — unable to mention `WalkedRow`.  This module
is the instantiation.

Three things are joined here, each already proved elsewhere.  `GroundedG` supplies the
memory-currency antecedent that `LocalStepFactG` demands; `LocalStepFactG` then supplies the pushed
state truth, which *is* the trajectory's successor together with its pc, ROM and configuration; and
`walkedRow_timeStep` with `start_injective` identify **which** index that successor sits at.  That
last step is the whole content of the "two indices" risk: the engine counts list positions and the
transcript counts timeline positions, and this is the one boundary where they are made the same
number.

What is deliberately *not* derived here is the row's own `EventStep`.  `LocalStepFactG` forgets it —
`LocalStateTruthG` says only that the trajectory reaches the next state, not which transition took
it there — and recovering it is arm-split: an ordinary row needs `¬ AboutToExecuteEcall`, a syscall
row needs the opposite plus its own `SyscallTransition`.  It is a hypothesis, discharged per arm by
the caller.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Execution
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The pc edge of a walked row, read off its `RowFacts` rather than off a `ChipRow`.

This is what replaces `pcEdgeOf` on the mixed carrier.  For an instruction row the two agree —
`statePullMessage_pcBits`/`statePushMessage_pcBits` identify the `RowFacts` messages with the
`ChipRow` projections — and a syscall row, which has no `ChipRow` at all, supplies the same two
messages through `syscallRowFacts`. -/
noncomputable def walkedPcEdge (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (row : WalkedRow p) : BitVec 64 × BitVec 64 :=
  (StateMsg.pcBits (WalkedRow.facts g row).statePull,
    StateMsg.pcBits (WalkedRow.facts g row).statePush)

/-- The walk's own per-row output, plus the row's arm-split `EventStep`, is exactly the engine's
positioned advance obligation. -/
theorem walkAdvancesAt_of_walk (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (data : ProverData (ZMod p)) (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p)) (initial : SailState) (initialClock : ℕ)
    (currencyAt : ∀ (k : ℕ) (hk : k < rows.length),
      ∀ mp ∈ (WalkedRow.facts g (rows[k]'hk)).memPulls,
        SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
        SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG (eventTrajectory handler prog (transcriptOf data rows) initial) initial
          (eventTimeline (transcriptOf data rows) initialClock)
          (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (stepAt : ∀ (k : ℕ) (hk : k < rows.length),
      LocalStepFactG prog (eventTrajectory handler prog (transcriptOf data rows) initial) initial
        (eventTimeline (transcriptOf data rows) initialClock)
        (WalkedRow.facts g (rows[k]'hk)))
    (widthAt : ∀ (k : ℕ) (hk : k < rows.length),
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePush
        = StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull + (rows[k]'hk).duration)
    (pullAt : ∀ (k : ℕ) (hk : k < rows.length),
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
        = (eventTimeline (transcriptOf data rows) initialClock).start k)
    (stepOf : ∀ (k : ℕ) (hk : k < rows.length) (state next : SailState),
      eventTrajectory handler prog (transcriptOf data rows) initial k = some state →
      eventTrajectory handler prog (transcriptOf data rows) initial (k + 1) = some next →
      state.regs.get? Register.PC = some (walkedPcEdge g (rows[k]'hk)).1 →
      RomLoaded prog state → SailConfigured state →
      EventStep handler.relation prog state (rows[k]'hk).event next ∧
        ((rows[k]'hk).event = ExecutionEvent.ordinary →
          SupportedSP1Transition prog ⟨state, ⟨(rows[k]'hk).event, next⟩⟩)) :
    WalkAdvancesAt handler.relation prog WalkedRow.event (walkedPcEdge g)
      (eventTrajectory handler prog (transcriptOf data rows) initial) rows := by
  intro done row suffix rowsEq state position pcRow romState cfgState
  subst rowsEq
  have hk : done.length < (done ++ row :: suffix).length := by simp
  have hrow : ((done ++ row :: suffix)[done.length]'hk) = row := by simp
  -- The walk's per-row facts, restated at this row's spelling.
  have currency := currencyAt done.length hk
  have stepRow := stepAt done.length hk
  have widthRow := widthAt done.length hk
  have pullRow := pullAt done.length hk
  have timeStep := walkedRow_timeStep data g (done ++ row :: suffix) initialClock done.length hk
    pullRow widthRow
  rw [hrow] at currency stepRow widthRow pullRow timeStep
  -- The row's pull truth, pinned to the engine's own state and index.
  simp only [walkedPcEdge, StateMsg.pcBits] at pcRow
  have pullTruth : LocalStateTruthG prog
      (eventTrajectory handler prog (transcriptOf data (done ++ row :: suffix)) initial)
      (eventTimeline (transcriptOf data (done ++ row :: suffix)) initialClock)
      (WalkedRow.facts g row).statePull :=
    ⟨done.length, state, position, pullRow, pcRow, romState, cfgState⟩
  -- The pushed truth is the trajectory's successor; `start_injective` says at which index.
  obtain ⟨n', next, nextTraj, pushTime, nextPc, nextRom, nextCfg⟩ :=
    (stepRow pullTruth currency).1
  have nEq : n' = done.length + 1 :=
    start_injective _ (pushTime.symm.trans (timeStep done.length pullRow))
  subst nEq
  obtain ⟨eventStep, routed⟩ :=
    stepOf done.length hk state next position nextTraj
      (by simp only [walkedPcEdge, StateMsg.pcBits, hrow]; exact pcRow)
      romState cfgState
  rw [hrow] at eventStep routed
  exact ⟨next, nextTraj, eventStep, by simpa only [walkedPcEdge, StateMsg.pcBits] using nextPc,
    nextRom, nextCfg, routed⟩

/-- **The mixed shard's proof-free execution trace.**

The engine reports its events as `rows.map WalkedRow.event`, which is *definitionally*
`transcriptOf data rows` — `transcriptOf_eq_map` is `rfl`.  So this produces the very transcript the
whole syscall layer is already stated over, rather than a parallel one that would then have to be
proved equal to it.  That is the same discipline as `walkAdvancesAt_of_walk`, one level up: make the
two spellings one term by construction instead of reconciling them afterwards. -/
theorem walkedExecution_of_advances (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (data : ProverData (ZMod p)) (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p)) (initial : SailState) (initialPc finalPc : BitVec 64)
    (advances : WalkAdvancesAt handler.relation prog WalkedRow.event (walkedPcEdge g)
      (eventTrajectory handler prog (transcriptOf data rows) initial) rows)
    (walk : Walk.IsWalk (walkedPcEdge g) initialPc finalPc rows)
    (pc : initial.regs.get? Register.PC = some initialPc)
    (rom : RomLoaded prog initial) (cfg : SailConfigured initial) :
    ∃ execution : Machine.EventExecutionTrace,
      execution.initialState = initial ∧
      execution.events = transcriptOf data rows ∧
      execution.finalState.regs.get? Register.PC = some finalPc ∧
      execution.Valid handler.relation prog ∧
      AllTransitionsSupported prog execution :=
  walkExecution_of_advances handler.relation prog WalkedRow.event (walkedPcEdge g)
    (eventTrajectory handler prog (transcriptOf data rows) initial) rows initial initialPc finalPc
    advances walk rfl pc rom cfg

/-- The trace's per-transition widths are the walk's own row widths.

`WalkedRow.duration_event` is the whole content: a row's window and the duration its event reports
agree arm for arm, because `WalkedRow` and `ExecutionEvent` are the same two-way split. -/
theorem walkedExecution_durations (data : ProverData (ZMod p)) (rows : List (WalkedRow p))
    (execution : Machine.EventExecutionTrace)
    (events : execution.events = transcriptOf data rows) :
    execution.transitions.map (fun transition => transition.event.duration)
      = rows.map WalkedRow.duration := by
  have base : execution.transitions.map Machine.EventTransition.event
      = rows.map WalkedRow.event := events
  calc execution.transitions.map (fun transition => transition.event.duration)
      = (execution.transitions.map Machine.EventTransition.event).map
          Machine.ExecutionEvent.duration := by rw [List.map_map]; rfl
    _ = (rows.map WalkedRow.event).map Machine.ExecutionEvent.duration := by rw [base]
    _ = rows.map WalkedRow.duration := by
          rw [List.map_map]
          exact List.map_congr_left fun row _ => WalkedRow.duration_event row

/-- The mixed trace's final clock is the walk's own prefix-summed row widths.

This is where the 264-tick row is actually paid for: `transitions_finalClock` sums the trace's own
event durations with no ordinary hypothesis at all.  Nothing in the chain knows that 8 is a special
number. -/
theorem walkedExecution_finalClock (data : ProverData (ZMod p)) (rows : List (WalkedRow p))
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ)
    (events : execution.events = transcriptOf data rows) :
    execution.finalClock initialClock
      = initialClock + (rows.map WalkedRow.duration).sum := by
  change Machine.clockAfterEvents initialClock
    (execution.transitions.map Machine.EventTransition.event) = _
  rw [transitions_finalClock, walkedExecution_durations data rows execution events]

/-- The mixed trace's schedule discipline, from each row's own `StartsAt`.

The obligation is arm-split by construction and cannot be otherwise: an instruction row owes
nothing, because an ordinary event's `StartsAt` is `True`; a syscall row owes
`event.clock = ` its own prefix sum, which `syscallEvent_startsAt` derives from the row's `Spec`
limb bounds and `2 ^ 24 < p`.  That is precisely the fact a row-generic engine cannot produce, which
is why it enters here as a hypothesis rather than as a conclusion. -/
theorem walkedExecution_clocked (data : ProverData (ZMod p)) (rows : List (WalkedRow p))
    (execution : Machine.EventExecutionTrace) (initialClock : ℕ)
    (events : execution.events = transcriptOf data rows)
    (starts : ∀ (k : ℕ) (hk : k < rows.length),
      (rows[k]'hk).event.StartsAt
        (initialClock + ((rows.take k).map WalkedRow.duration).sum)) :
    execution.Clocked initialClock := by
  have base : execution.transitions.map Machine.EventTransition.event
      = rows.map WalkedRow.event := events
  have durations := walkedExecution_durations data rows execution events
  have lengths : execution.transitions.length = rows.length := by
    simpa using congrArg List.length base
  refine Machine.eventTransitionsClocked_of_starts execution.transitions initialClock ?_
  intro k hk
  have hk' : k < rows.length := lengths ▸ hk
  have eventEq : (execution.transitions[k]'hk).event = (rows[k]'hk').event := by
    have h := List.getElem_of_eq base (i := k) (by simpa using hk)
    simpa using h
  have takeEq : ((execution.transitions.take k).map fun t => t.event.duration)
      = (rows.take k).map WalkedRow.duration := by
    rw [List.map_take, durations, ← List.map_take]
  rw [eventEq, takeEq]
  exact starts k hk'

/-- Discharge the engine's per-position `EventStep` obligation, arm by arm.

Neither arm can be handled generically, and they fail differently.  An ordinary row needs
`¬ AboutToExecuteEcall` — which comes from its own routing evidence, not from the trajectory — plus
the determinism step that identifies its `advance`'s target with the trajectory's.  A syscall row
needs the *opposite* ecall fact, from `SyscallRowContext`, plus its payload's `SyscallTransition`;
there the determinism is free, because `ExecutableSyscallHandler.relation` is definitionally
`run = some` and the trajectory's successor is that same `run`.

The instruction arm's premise is stated as "this row advances and routes" rather than as a
`GroundedRow`, so this lemma stays clear of the wiring/carrier layer; the caller supplies it from
`GroundedRow.advance` and `GroundedRow.supportedSP1Transition`. -/
theorem stepOf_of_arms (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (data : ProverData (ZMod p)) (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p)) (initial : SailState)
    (payload : SyscallAdvancePayload (p := p) handler)
    (instructionAt : ∀ (k : ℕ) (hk : k < rows.length) (row : DecodedInstructionRow p),
      (rows[k]'hk) = WalkedRow.instruction row →
      ∀ state : SailState,
        state.regs.get? Register.PC = some (walkedPcEdge g (rows[k]'hk)).1 →
        RomLoaded prog state → SailConfigured state →
        ∃ target, SailStep state target ∧
          SupportedSP1Transition prog ⟨state, ⟨ExecutionEvent.ordinary, target⟩⟩)
    (syscallAt : ∀ (k : ℕ) (hk : k < rows.length) (r : SyscallInstrsChip.Inputs (ZMod p)),
      (rows[k]'hk) = WalkedRow.syscall r →
      ∀ state : SailState,
        eventTrajectory handler prog (transcriptOf data rows) initial k = some state →
        r.is_real = 1 ∧ SyscallInstrsChip.Spec r ∧ SyscallInstrsChip.SelectorsValid r ∧
          SyscallInstrsChip.PulledFacts r ∧ (syscallEventOfRow r).IsInlineCanonical ∧
          SyscallRowContext r prog state) :
    ∀ (k : ℕ) (hk : k < rows.length) (state next : SailState),
      eventTrajectory handler prog (transcriptOf data rows) initial k = some state →
      eventTrajectory handler prog (transcriptOf data rows) initial (k + 1) = some next →
      state.regs.get? Register.PC = some (walkedPcEdge g (rows[k]'hk)).1 →
      RomLoaded prog state → SailConfigured state →
      EventStep handler.relation prog state (rows[k]'hk).event next ∧
        ((rows[k]'hk).event = ExecutionEvent.ordinary →
          SupportedSP1Transition prog ⟨state, ⟨(rows[k]'hk).event, next⟩⟩) := by
  intro k hk state next now nextTraj pcRow romState cfgState
  have hev : (transcriptOf data rows)[k]? = some (rows[k]'hk).event :=
    transcriptOf_getElem? data rows k hk
  cases hrow : (rows[k]'hk) with
  | instruction row =>
      obtain ⟨target, targetStep, supported⟩ :=
        instructionAt k hk row hrow state pcRow romState cfgState
      have hOrdinary : (transcriptOf data rows)[k]? = some ExecutionEvent.ordinary := by
        rw [hev, hrow]; rfl
      have trajStep :=
        sailStep_of_eventTrajectory_ordinary handler prog (transcriptOf data rows) initial
          hOrdinary now nextTraj
      have targetEq : target = next :=
        Option.some.inj ((TimedGrounding.stepOnce_of_sailStep targetStep).symm.trans
          (TimedGrounding.stepOnce_of_sailStep trajStep))
      subst targetEq
      exact ⟨.ordinary supported.notAboutToExecuteEcall trajStep, fun _ => supported⟩
  | syscall r =>
      obtain ⟨real, spec, sel, pulled, canonical, context⟩ := syscallAt k hk r hrow state now
      obtain ⟨target, transition, -⟩ :=
        payload r prog state real spec sel pulled canonical cfgState romState context
      have hSyscall : (transcriptOf data rows)[k]?
          = some (ExecutionEvent.syscall (syscallEventOfRow r)) := by
        rw [hev, hrow]; rfl
      have run :=
        handlerRun_of_eventTrajectory_syscall handler prog (transcriptOf data rows) initial
          hSyscall now nextTraj
      have targetEq : target = next := Option.some.inj (transition.2.2.symm.trans run)
      subst targetEq
      exact ⟨.syscall context.ecall transition, fun h => absurd h (by simp [WalkedRow.event])⟩

end SP1Clean.Soundness
