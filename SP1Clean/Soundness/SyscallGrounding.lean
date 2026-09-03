import SP1Clean.Soundness.SyscallRowSemantics
import SP1Clean.Soundness.GenericWalk
import SP1Clean.Soundness.GroundingAdapter

/-! # Grounding a syscall row

An ordinary instruction row reaches the walk through `ChipKind.advance`, whose payload is
`∃ s', SailStep s s' ∧ RowEffect prog view s s'`. Neither conjunct survives for a syscall row:
`SailStep` is the thing SP1's ECALL is not, and `RowEffect`'s **first field** is
`normal : SailRetiresNormally`, which asserts the same thing again.

So the syscall analogue is a different payload, not a variant of `advance`. This file states it,
together with the three duration generalizations the walk needs once a row can be 264 ticks wide.

**Three couplings worth naming, because each is new.**

*The clock.* `EventTransitionsClocked` checks `ExecutionEvent.StartsAt`, which is `True` for an
ordinary event but `event.clock = clock` for a syscall. This is the first place the *semantic*
transcript clock and the *bus* clock the trail walks are forced to be the same number — for ordinary
rows they are independent, which is why `ordinaryTransitions_clocked` is a one-liner today.

*The window.* A row's whole memory activity must fit `[t, t+4]` (`TouchOK`), regardless of how wide
its clock window is. SP1's syscall register slots sit at offsets 4/3/2, so they fit — and a
*precompile* with activity in the 256-tick interior would not. That is the structural reason the
thirteen inline codes are the boundary of this work.

*Alignment.* Every duration is a multiple of eight (`264 = 8·33`), so a mid-shard syscall row leaves
every later row's `align8` residue untouched. That is what lets the alignment machinery transfer
with a hypothesis change rather than a redesign. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The row effect a syscall has

`RowEffect` minus its Sail-retirement field, with the pc and register clauses reading the *event*
rather than the row's decoded commit — because for a syscall the handler, not `try_step`, is what
moved the machine. -/

/-- What a syscall row does to the machine: the pc goes to the event's `nextPc`, `t0` receives the
event's `result`, every other register and all of memory are untouched, and the platform
configuration survives. -/
structure SyscallRowEffect (event : CoreSyscallEvent) (s s' : SailState) : Prop where
  pc : s'.regs.get? Register.PC = some event.nextPc
  t0 : s'.get_reg? 5#5 = some event.result
  otherRegs : ∀ idx : BitVec 5, idx ≠ 5#5 → s'.get_reg? idx = s.get_reg? idx
  mem : ∀ a : ℕ, s'.mem.get? a = s.mem.get? a
  init : s.isInitialized → s'.isInitialized
  cfg : SailConfigured s → SailConfigured s'

/-- The syscall analogue of `ChipKind.AdvancePayload`. Two differences carry the whole content:
there is no `SailStep`, and the handler is a parameter — `ChipKind` mentions only a program and a
state today, while `SyscallTransition` needs the model's handler. -/
def SyscallAdvancePayload (handler : ExecutableSyscallHandler) : Prop :=
  ∀ (r : SyscallInstrsChip.Inputs (ZMod p)) (prog : GuestProgram) (s : SailState),
    r.is_real = 1 →
    SyscallInstrsChip.Spec r →
    SyscallInstrsChip.SelectorsValid r →
    SyscallInstrsChip.PulledFacts r →
    (syscallEventOfRow r).IsInlineCanonical →
    SailConfigured s → RomLoaded prog s →
    SyscallRowContext r prog s →
    ∃ s',
      Machine.SyscallTransition handler.relation prog (syscallEventOfRow r) s s' ∧
      SyscallRowEffect (syscallEventOfRow r) s s'

/-- The payload holds for the thirteen-arm handler — this is `syscallTransition_of_row` packaged in
the shape the grounding engine consumes. -/
theorem syscallAdvancePayload_full :
    SyscallAdvancePayload (p := p) ExecutableSyscallHandler.full := by
  -- SKETCH (L3): `syscallTransition_of_row` gives the transition and the target; the row effect
  -- reads off the handler's two register inserts.
  sorry

/-! ## The row's facts, and its step obligation -/

/-- The `RowFacts` a syscall row contributes: its State edge and its three register touches. Unlike
the halt table's, these are ordinary walked touches — later rows re-read `x5`/`x10`/`x11`, so the
frontier records this row pushes are consumed rather than final. -/
noncomputable def syscallRowFacts (r : SyscallInstrsChip.Inputs (ZMod p)) : RowFacts p :=
  { statePull := SyscallInstrsChip.statePulledMessage r
    statePush := SyscallInstrsChip.statePushedMessage r
    fetch := SyscallInstrsChip.programMessage r
    memPulls := []   -- SKETCH (L3): the three read-priors, each at the row's own pull time
    memPushes := [] }  -- SKETCH (L3): the three read-backs at offsets 4/3/2

/-- **The syscall row's step fact**, at the event trajectory. This is the syscall analogue of
`stepFact_of_advance`, and the reason the walk had to be parameterized: its conclusion is
`LocalStateTruthG` at a trajectory whose step here is the handler, not `try_step`. -/
theorem syscallStepFact_of_advance (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (r : SyscallInstrsChip.Inputs (ZMod p))
    (payload : SyscallAdvancePayload (p := p) handler) :
    LocalStepFactG prog (eventTrajectory handler prog events initial) initial
      (eventTimeline events initialClock) (syscallRowFacts r) := by
  -- SKETCH (L3): destructure the pulled truth to get the step index `n` and the state; fire the
  -- payload there; the pushed state is `eventTrajectory … (n+1)` because `events[n]` is this row's
  -- `.syscall` event, so the trajectory's own successor *is* the handler's target.
  sorry

/-- The row's shape obligations — with the two premises a 264-tick row genuinely cannot supply
itself, which the sketch's hypothesis-free statement hid.

**`align8` is a walk fact, not a row fact.** It relates this row's pull to the *shard's* initial
clock, which no single row can see; the walk establishes it inductively as rows chain.

**`timeGap` needs the bump chip.** Upstream computes the pushed clock as `clk_low + 264` with no
range constraint, and *`clk_low + 264` may exceed `2 ^ 24`* — the same deliberate non-canonicality
as `next_pc[0] = pc[0] + 4` without a carry, legalized downstream by `StateBumpChip`
(`air.rs:129-140`, `adapter/bump.rs:185-247`). So on a wrapping row the pushed message's `timeNat`
is *not* `pull + 264`, and the 264 has to arrive as a canonicalization premise exactly as the pc's
`+ 4` carry does in `SyscallRowContext`. `ClkDiscipline` does not cover it: that discipline is
stated for offsets `≤ 4`, which is the intra-row effect range, not the window width.

The remaining four fields are vacuous while `syscallRowFacts` has no touches, and become the
offset-4/3/2 register slots when it gains them. -/
theorem syscallRowOKCore (initialClock : ℕ) (r : SyscallInstrsChip.Inputs (ZMod p))
    (align : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) % 8 = initialClock % 8)
    (canonicalClock : StateMsg.timeNat (SyscallInstrsChip.statePushedMessage r)
      = StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 264) :
    TimedGrounding.RowOKCore initialClock (syscallRowFacts r) := by
  sorry

/-! ## The duration generalizations

Three statements in the engine are pinned to exactly eight ticks. Each has a duration-generic form,
and in two cases the generic form is *already there* — only the `+8` wrapper is used. -/

/-- `statePullAlign8_of_stateWalk` with the exact `+8` step replaced by "each row's window is a
multiple of eight". Named by the engine audit as the easiest and most necessary of the three. -/
theorem statePullAlign8_of_durations {α : Type} (rows : List α)
    (duration : α → ℕ) (_dvd : ∀ d ∈ rows, 8 ∣ duration d) :
    True := by
  -- SKETCH (L3): mirror `statePullAlign8_of_stateWalk` (`GroundingInternal.lean:446`), deriving the
  -- residue from `statePullTime_of_stateWalk_durations` plus `8 ∣ duration` instead of from the
  -- exact step. Stated as `True` here only until the walk's row type is fixed at L4.
  trivial

/-- `Timeline.start` is injective, because it strictly increases. Stated here rather than in
`MicroTime.lean` only to avoid a rebuild of everything below during the sketch phase; it belongs
beside `start_lt_of_lt`. -/
private theorem start_injective (tl : Semantics.Timeline) : Function.Injective tl.start := by
  intro a b h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (tl.start_lt_of_lt hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (tl.start_lt_of_lt hgt))

/-- One step of the transcript's timeline is that step's own duration — the prefix sum, unrolled
once. This is the identity that makes the walk's positions and the timeline's starts one
arithmetic. -/
private theorem eventTimeline_start_succ (events : List ExecutionEvent) (initialClock k : ℕ) :
    (Semantics.eventTimeline events initialClock).start (k + 1)
      = (Semantics.eventTimeline events initialClock).start k + Semantics.durationAt events k := by
  simp only [Semantics.eventTimeline_start]
  rw [List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The transcript's timeline agrees with the walk's positions: a row at trail index `k` pulls at
`tl.start k` and pushes at `tl.start (k+1)`. This is `walkG`'s timeline hypothesis, and the index is
unique because `Timeline.start` strictly increases. -/
theorem timelineAgreement_of_durations (events : List ExecutionEvent) (initialClock : ℕ)
    (r : RowFacts p) (k : ℕ)
    (hpull : StateMsg.timeNat r.statePull = (eventTimeline events initialClock).start k)
    (hpush : StateMsg.timeNat r.statePush
      = StateMsg.timeNat r.statePull + Semantics.durationAt events k) :
    ∀ n : ℕ, StateMsg.timeNat r.statePull = (eventTimeline events initialClock).start n →
      StateMsg.timeNat r.statePush = (eventTimeline events initialClock).start (n + 1) := by
  intro n hn
  have hnk : n = k := start_injective _ (hn.symm.trans hpull)
  subst hnk
  rw [hpush, hpull, eventTimeline_start_succ]

/-! ## The transcript

Building the event list from the ordered rows is what ties the semantic clock to the bus clock. -/

/-- The event a walked row denotes: `.ordinary` for an instruction row, `.syscall` for a syscall row.
`durationAt` on the resulting transcript is then the row's own window width, which is what makes the
timeline and the walk's positions the same arithmetic. -/
inductive WalkedRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)]
  | instruction (row : DecodedInstructionRow p)
  | syscall (r : SyscallInstrsChip.Inputs (ZMod p))

/-- The clock window a walked row occupies. Unlike `SyscallTrailRow.duration` this is total on the
type — there is no zero-width arm — which is exactly why the transcript identity below holds
unconditionally here and needs a side condition on the trail. -/
def WalkedRow.duration : WalkedRow p → ℕ
  | .instruction _ => 8
  | .syscall _ => 264

/-- The transcript a walk order denotes. -/
noncomputable def transcriptOf (_data : ProverData (ZMod p)) (rows : List (WalkedRow p)) :
    List ExecutionEvent :=
  rows.map fun row =>
    match row with
    | .instruction _ => .ordinary
    | .syscall r => .syscall (syscallEventOfRow r)

/-- **Each walked row's own window is the duration its event reports at the same index.** This is
the identity that lets the walk's positions be read off the timeline and vice versa, and it is what
`walkE` needs at every index. It holds arm for arm because `WalkedRow` and `ExecutionEvent` are the
same two-way split. -/
theorem durationAt_transcriptOf (data : ProverData (ZMod p)) (rows : List (WalkedRow p)) (k : ℕ)
    (hk : k < rows.length) :
    Semantics.durationAt (transcriptOf data rows) k = (rows[k]'hk).duration := by
  have hlen : k < (transcriptOf data rows).length := by simpa [transcriptOf] using hk
  rw [Semantics.durationAt, List.getElem?_eq_getElem hlen]
  simp only [transcriptOf, List.getElem_map]
  cases rows[k] <;> rfl

/-- The clock coupling, stated where it can be checked: a syscall row's event carries the very clock
its State pull sits at, which is what `EventTransitionsClocked` demands and what an ordinary row gets
for free. -/
theorem syscallEvent_startsAt (r : SyscallInstrsChip.Inputs (ZMod p))
    (spec : SyscallInstrsChip.Spec r) (real : r.is_real = 1) :
    (ExecutionEvent.syscall (syscallEventOfRow r)).StartsAt
      (StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)) := by
  -- SKETCH (L3): `decodeSyscallRow`'s `clock` field is `values[0]·2^24 + values[1]·2^16 + values[2]`,
  -- which is `clk_high`/`clk_16_24`/`clk_0_16`. That is *not* definitionally the pulled message's
  -- `timeNat`: the message carries the two low limbs already recombined as
  -- `clk_0_16 + clk_16_24 * 65536`, so the two agree only once that field addition is known not to
  -- wrap — which is what `CPUState.Spec`'s `clk_0_16 < 2 ^ 16` / `clk_16_24 < 2 ^ 8` bounds give,
  -- and why this statement now takes the row's `Spec`.
  sorry

end SP1Clean.Soundness
