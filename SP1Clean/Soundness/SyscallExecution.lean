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

end SP1Clean.Soundness
