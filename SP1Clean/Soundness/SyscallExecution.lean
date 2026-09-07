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
open Air.Flat

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

/-! ## The walk feed's per-row obligations, from the ensemble

Everything below reads the *witness*, so it needs the field bound the syscall row's clock
recombination needs (`2 ^ 24 < p`, from the ambient `2 ^ 25`), where the engine plumbing above is
content with `2 ^ 17`.  Keeping that in a section rather than in the file's variable block is what
stops the plumbing from inheriting a bound it does not use. -/

section WitnessObligations

variable [Fact (2 ^ 25 < p)]

-- Named rather than anonymous, for the reason `SyscallWiring` records: `local` scopes the *use*,
-- not the generated declaration name, so two anonymous instances in one namespace collide.
local instance syscallExecution_fact_24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Each walked row's window is its own duration.

This is `walkE`'s `widthAt` input, and the first place the two arms' genuinely *different* clock
contracts have to be presented as one statement: `+8` for an instruction row
(`witness_realDecodedInstructionRows_timeStep`) against `+264` for a syscall row
(`witness_realSyscallInstrsRows_timeStep`).  The aligned carrier costs nothing here — `AlignsWith`
fixes both State messages on the nose and reorders only the memory lists. -/
theorem walkedRow_widthAt (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (g : DecodedInstructionRow p → Semantics.RowFacts p) (rows : List (WalkedRow p))
    (aligned : ∀ row : DecodedInstructionRow p, WalkedRow.instruction row ∈ rows →
      TimedGrounding.AlignsWith (g row) (row.ordinaryRowFacts witness.data))
    (instructionSource : ∀ row : DecodedInstructionRow p, WalkedRow.instruction row ∈ rows →
      row ∈ realDecodedInstructionRows witness.data witness.tables)
    (syscallSource : ∀ r : SyscallInstrsChip.Inputs (ZMod p), WalkedRow.syscall r ∈ rows →
      ∃ raw ∈ realSyscallInstrsRows witness,
        r = syscallInstrsRow (syscallInstrsTable witness) raw) :
    ∀ (k : ℕ) (hk : k < rows.length),
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePush
        = StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
          + (rows[k]'hk).duration := by
  intro k hk
  have hmem : (rows[k]'hk) ∈ rows := List.getElem_mem hk
  cases hrow : (rows[k]'hk) with
  | instruction row =>
      rw [hrow] at hmem
      have align := aligned row hmem
      have step := witness_realDecodedInstructionRows_timeStep witness constraints balanced row
        (instructionSource row hmem)
      simp only [WalkedRow.facts, WalkedRow.duration]
      rw [align.statePush, align.statePull]
      exact step
  | syscall r =>
      rw [hrow] at hmem
      obtain ⟨raw, rawMem, rfl⟩ := syscallSource r hmem
      -- ⚠ Rewrite with the `RowFacts` projections rather than letting `exact` reach the messages by
      -- defeq: `syscallInstrsRow` unfolds into the table's element construction, and crossing that
      -- at a witness row exceeds the depth budget (see the campaign's crossing rule).
      simp only [WalkedRow.facts, WalkedRow.duration, syscallRowFacts_statePush,
        syscallRowFacts_statePull]
      exact witness_realSyscallInstrsRows_timeStep witness constraints balanced raw rawMem

omit [Fact (2 ^ 17 < p)] in
/-- **The syscall arm's row-local engine contract, from the witness.**

`syscallRowOKCore` takes ten premises; nine are witness facts already proved elsewhere — `is_real`
from table membership, `Spec` through the currency break, the two clock-byte bounds from the
composed `CPUState` reader, the three operand indices from the committed `ECALL` Program row, and
the `+264` step.

The one that stays a hypothesis is `align8`, and it stays for a reason worth naming: it relates the
row's pull to the **shard's** initial clock, which no single row can see.  Only the walk establishes
it, inductively, which is why it cannot be discharged here however many witness facts are in hand. -/
theorem syscallRowOKCore_of_witness (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness) (initialClock : ℕ)
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1)
    (align : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow (syscallInstrsTable witness) row)) % 8 = initialClock % 8) :
    TimedGrounding.RowOKCore initialClock
      (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)) := by
  obtain ⟨tableMem, real⟩ := mem_realSyscallInstrsRows witness rowMem
  obtain ⟨clk0B, clk1B⟩ := syscallInstrsRow_cpuState_bounds witness constraints balanced rowMem
  obtain ⟨opA, opB, opC⟩ :=
    syscallInstrsRow_operands witness constraints balanced providerBound rowMem
  have spec := syscallInstrsRow_spec_of_pullCurrency witness constraints balanced tableMem currency
  have step := witness_realSyscallInstrsRows_timeStep witness constraints balanced row rowMem
  -- ⚠ **Interpose an opaque variable before applying the abstract-row lemma.**  Every premise above
  -- is cheap to derive and the application is cheap at an abstract row, but doing both at the
  -- *concrete* row costs 372k `Vector.mapRange` unfoldings: the clock-bound premise and
  -- `syscallRowOKCore`'s expectation of it differ enough that `whnf` starts normalizing the table's
  -- element construction (`[def_eq] sp1Ensemble` in the diagnostics).  With the row generalized to
  -- a bare `r` nothing can unfold it, and the proof elaborates in ~2s.
  generalize syscallInstrsRow (syscallInstrsTable witness) row = r
    at real clk0B clk1B opA opB opC spec step align ⊢
  exact syscallRowOKCore initialClock r real spec clk0B clk1B opA opB opC align step

omit [Fact (2 ^ 17 < p)] in
/-- **The syscall arm's step fact, from the witness.**

Ten of `syscallStepFact_of_advance`'s premises are witness facts; the three that remain are exactly
the ones no row-local reasoning can supply.  `payload` is the handler's own semantics.  `positioned`
says this row's window is the transcript slot carrying *this* row's event — a fact about the walk
order, not about the row.  And `rowContext` needs the trajectory's state at the row's index, plus
the `StateBumpChip` pc-carry premise. -/
theorem syscallStepFact_of_witness (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness)
    (canonicalCodes : SP1Clean.CoreProfile.CanonicalSyscallCodes (syscallEventsOf witness))
    (payload : SyscallAdvancePayload (p := p) handler)
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1)
    (positioned : ∀ n : ℕ,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
          (syscallInstrsRow (syscallInstrsTable witness) row))
        = (eventTimeline events initialClock).start n →
      events[n]? = some (ExecutionEvent.syscall
        (syscallEventOfRow (syscallInstrsRow (syscallInstrsTable witness) row))))
    (rowContext : ∀ (n : ℕ) (s : SailState),
      eventTrajectory handler prog events initial n = some s →
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
          (syscallInstrsRow (syscallInstrsTable witness) row))
        = (eventTimeline events initialClock).start n →
      SyscallRowContext (syscallInstrsRow (syscallInstrsTable witness) row) prog s) :
    LocalStepFactG prog (eventTrajectory handler prog events initial) initial
      (eventTimeline events initialClock)
      (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)) := by
  obtain ⟨tableMem, real⟩ := mem_realSyscallInstrsRows witness rowMem
  obtain ⟨clk0B, clk1B⟩ := syscallInstrsRow_cpuState_bounds witness constraints balanced rowMem
  obtain ⟨opA, -, -⟩ :=
    syscallInstrsRow_operands witness constraints balanced providerBound rowMem
  have spec := syscallInstrsRow_spec_of_pullCurrency witness constraints balanced tableMem currency
  have pulled := syscallInstrsRow_pulledFacts witness constraints balanced tableMem currency
  have canonical := isInlineCanonical_of_profile witness canonicalCodes rowMem
  have u64A := syscallInstrsRow_opAValue_isU64 witness constraints balanced rowMem
  have step := witness_realSyscallInstrsRows_timeStep witness constraints balanced row rowMem
  have sel := SyscallInstrsChip.Spec.selectorsValid spec
  generalize syscallInstrsRow (syscallInstrsTable witness) row = r
    at real clk0B clk1B opA spec pulled canonical u64A step sel positioned rowContext ⊢
  exact syscallStepFact_of_advance handler prog events initial initialClock r payload real spec sel
    pulled canonical clk0B clk1B u64A opA positioned rowContext step

omit [Fact (2 ^ 17 < p)] in
/-- **The syscall arm's frame fact, from the witness.**  The step fact's twin, with the same three
irreducible hypotheses; it needs neither the clock-byte bounds nor `op_a`'s `isU64`, because a frame
claim never touches the written value. -/
theorem syscallFrameFact_of_witness (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (providerBound : ProgramProviderBound witness)
    (canonicalCodes : SP1Clean.CoreProfile.CanonicalSyscallCodes (syscallEventsOf witness))
    (payload : SyscallAdvancePayload (p := p) handler)
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1)
    (positioned : ∀ n : ℕ,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
          (syscallInstrsRow (syscallInstrsTable witness) row))
        = (eventTimeline events initialClock).start n →
      events[n]? = some (ExecutionEvent.syscall
        (syscallEventOfRow (syscallInstrsRow (syscallInstrsTable witness) row))))
    (rowContext : ∀ (n : ℕ) (s : SailState),
      eventTrajectory handler prog events initial n = some s →
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
          (syscallInstrsRow (syscallInstrsTable witness) row))
        = (eventTimeline events initialClock).start n →
      SyscallRowContext (syscallInstrsRow (syscallInstrsTable witness) row) prog s) :
    FrameFactG prog (eventTrajectory handler prog events initial) initial
      (eventTimeline events initialClock)
      (syscallRowFacts (syscallInstrsRow (syscallInstrsTable witness) row)) := by
  obtain ⟨tableMem, real⟩ := mem_realSyscallInstrsRows witness rowMem
  obtain ⟨opA, -, -⟩ :=
    syscallInstrsRow_operands witness constraints balanced providerBound rowMem
  have spec := syscallInstrsRow_spec_of_pullCurrency witness constraints balanced tableMem currency
  have pulled := syscallInstrsRow_pulledFacts witness constraints balanced tableMem currency
  have canonical := isInlineCanonical_of_profile witness canonicalCodes rowMem
  have step := witness_realSyscallInstrsRows_timeStep witness constraints balanced row rowMem
  have sel := SyscallInstrsChip.Spec.selectorsValid spec
  generalize syscallInstrsRow (syscallInstrsTable witness) row = r
    at real opA spec pulled canonical step sel positioned rowContext ⊢
  exact syscallFrameFact_of_advance handler prog events initial initialClock r payload real spec sel
    pulled canonical opA positioned rowContext step

end WitnessObligations

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
