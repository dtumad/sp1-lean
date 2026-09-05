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

/-! ### The configuration frame under the handler's writes

Neither `Register.PC` nor `Register.x5` is a configuration CSR, so `SailConfigured` survives both of
the handler's inserts. `SailConfigured.congr` is the general tool; these two are its instances at the
shapes `ExecutableSyscallHandler.full` actually produces. -/

private theorem configFrame_pc (s : SailState) (v : RegisterType Register.PC)
    (c : SailConfigured s) :
    SailConfigured { s with regs := s.regs.insert Register.PC v } := by
  refine SP1Clean.Advance.SailConfigured.congr c (SailState.isInitialized_insert s c.init _ _) ?_
  intro R hR
  have hne : ¬((Register.PC == R) = true) := by
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  show (s.regs.insert Register.PC v).get? R = s.regs.get? R
  rw [Std.ExtDHashMap.get?_insert, dif_neg hne]

private theorem configFrame_pc_x5 (s : SailState) (v : RegisterType Register.PC)
    (w : RegisterType Register.x5) (c : SailConfigured s) :
    SailConfigured { s with regs := (s.regs.insert Register.PC v).insert Register.x5 w } := by
  refine SP1Clean.Advance.SailConfigured.congr c
    (SailState.isInitialized_insert _ (SailState.isInitialized_insert s c.init _ _) _ _) ?_
  intro R hR
  have hnePC : ¬((Register.PC == R) = true) := by
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hnex5 : ¬((Register.x5 == R) = true) := by
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  show ((s.regs.insert Register.PC v).insert Register.x5 w).get? R = s.regs.get? R
  rw [Std.ExtDHashMap.get?_insert, dif_neg hnex5, Std.ExtDHashMap.get?_insert, dif_neg hnePC]

/-- The payload holds for the thirteen-arm handler — `syscallTransition_of_row` packaged in the shape
the grounding engine consumes, with the row effect read off the handler's own inserts. The two
branches differ in exactly one place: HALT writes only the pc, so `x5` keeps the prior code and
`otherRegs` is total; every other arm writes `x5` too, and `otherRegs` holds off the destination. -/
theorem syscallAdvancePayload_full :
    SyscallAdvancePayload (p := p) ExecutableSyscallHandler.full := by
  intro r prog s real spec sel pulled canonical _cfg _rom ctx
  have htable : (syscallEventOfRow r).tableByte = 0 :=
    CoreSyscallEvent.tableByte_of_inlineCanonical canonical
  obtain ⟨target, hrun, htrans⟩ :=
    syscallTransition_of_row r prog s spec sel pulled real canonical ctx
  refine ⟨target, htrans, ?_⟩
  have hpcT : target.regs.get? Register.PC = some (syscallEventOfRow r).nextPc :=
    htrans.2.1.2.2.2.2.1
  have ht0 : target.get_reg? 5#5 = some (syscallEventOfRow r).result :=
    htrans.2.1.2.2.2.2.2
  by_cases h0 : (syscallEventOfRow r).syscallId = Machine.haltSyscallId
  · have heq : target = { s with regs := s.regs.insert Register.PC Machine.haltPc } := by
      rw [full_run_halt prog _ s htable h0] at hrun
      exact (Option.some.inj hrun).symm
    subst heq
    exact { pc := hpcT, t0 := ht0, otherRegs := fun idx _ => by simp, mem := fun _ => rfl, init := fun h => SailState.isInitialized_insert s h _ _, cfg := fun c => configFrame_pc s _ c }
  · have hmem : (syscallEventOfRow r).syscallId ∈ inlineSyscallIds :=
      inlineSyscallIds_exhaustive _ canonical
    have heq : target = { s with regs := (s.regs.insert Register.PC ((syscallEventOfRow r).pc + 4)).insert Register.x5 (syscallEventOfRow r).result } := by
      rw [full_run_inline prog _ s htable h0 hmem] at hrun
      exact (Option.some.inj hrun).symm
    subst heq
    refine { pc := hpcT, t0 := ht0, otherRegs := ?_, mem := fun _ => rfl, init := ?_, cfg := fun c => configFrame_pc_x5 s _ _ c }
    · intro idx hidx
      have hne : Register.x5 ≠ reg_idx_to_Register idx := by
        simp only [ne_eq, eq_comm (a := Register.x5), regidxToRegister_eq_x5_iff]
        exact hidx
      have h1 := SailState.get_reg?_insert_of_ne (s := { s with regs := s.regs.insert Register.PC ((syscallEventOfRow r).pc + 4) }) (v := (syscallEventOfRow r).result) hne
      simpa using h1
    · exact fun h => SailState.isInitialized_insert _ (SailState.isInitialized_insert s h _ _) _ _

/-! ## The row's facts, and its step obligation -/

/-- The `RowFacts` a syscall row contributes: its State edge and its three register touches. Unlike
the halt table's, these are ordinary walked touches — later rows re-read `x5`/`x10`/`x11`, so the
frontier records this row pushes are consumed rather than final.

⚠ **The three read micro-times are `t`, `t + 3`, `t + 2`, not uniformly `t`**, and that is forced
rather than stylistic. `op_a` is the `t0` *write*: its push carries `op_a_value`, which need not
equal the prior, so it can only satisfy `TouchOK.push_kind`'s second disjunct — the one that pins
the push at `t + writeOffset = t + 4` and leaves the read time free (any point of `[t, t + 3]`
observes pre-write content, so `t` is the natural choice). `op_b` and `op_c` are pure read-backs:
their pushes carry the prior word, so they take the *first* disjunct, which demands
`MemoryMsg.timeNat push = mp.2` — fixing their read times at `t + 3` and `t + 2`, the clocks SP1
gives those two accesses. `ordinaryRowFacts` can use one uniform read time precisely because no
instruction row mixes the two disjuncts this way. -/
noncomputable def syscallRowFacts (r : SyscallInstrsChip.Inputs (ZMod p)) : RowFacts p :=
  { statePull := SyscallInstrsChip.statePulledMessage r
    statePush := SyscallInstrsChip.statePushedMessage r
    fetch := SyscallInstrsChip.programMessage r
    memPulls :=
      [(SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)),
       (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 3),
       (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 2)]
    memPushes :=
      [SyscallInstrsChip.memPushedMessage r r.op_a 4 r.op_a_value,
       SyscallInstrsChip.memPushedMessage r r.op_b 3 r.op_b_memory.prev_value,
       SyscallInstrsChip.memPushedMessage r r.op_c 2 r.op_c_memory.prev_value] }

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem syscallRowFacts_statePull (r : SyscallInstrsChip.Inputs (ZMod p)) :
    (syscallRowFacts r).statePull = SyscallInstrsChip.statePulledMessage r := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem syscallRowFacts_statePush (r : SyscallInstrsChip.Inputs (ZMod p)) :
    (syscallRowFacts r).statePush = SyscallInstrsChip.statePushedMessage r := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem syscallRowFacts_fetch (r : SyscallInstrsChip.Inputs (ZMod p)) :
    (syscallRowFacts r).fetch = SyscallInstrsChip.programMessage r := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem syscallRowFacts_memPulls (r : SyscallInstrsChip.Inputs (ZMod p)) :
    (syscallRowFacts r).memPulls =
      [(SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)),
       (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 3),
       (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c,
          StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 2)] := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem syscallRowFacts_memPushes (r : SyscallInstrsChip.Inputs (ZMod p)) :
    (syscallRowFacts r).memPushes =
      [SyscallInstrsChip.memPushedMessage r r.op_a 4 r.op_a_value,
       SyscallInstrsChip.memPushedMessage r r.op_b 3 r.op_b_memory.prev_value,
       SyscallInstrsChip.memPushedMessage r r.op_c 2 r.op_c_memory.prev_value] := rfl

/-- Each of the row's six Memory records addresses a register, because the committed `ECALL` pins
the three operand columns. This is where `witness_syscallRow_ecallTruth` pays for itself: without
it `locOf` falls through to `.ram`, whose `readWindow = 0` and `writeOffset = 1` make the offset-3
read and the offset-4 write unrepresentable. -/
theorem syscallRow_locOf_reg (r : SyscallInstrsChip.Inputs (ZMod p))
    {idx : ZMod p} {i : BitVec 5} (hidx : ((i.toNat : ℕ) : ZMod p) = idx)
    (block : Extracted.RegisterAccessCols (ZMod p)) (v : Word (ZMod p)) (c : ZMod p) :
    Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPulledMessage r block idx) = Semantics.MemLoc.reg i ∧
      Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPushedMessage r idx c v)
        = Semantics.MemLoc.reg i :=
  ⟨Semantics.MemoryMsg.locOf_register _ i hidx rfl rfl,
   Semantics.MemoryMsg.locOf_register _ i hidx rfl rfl⟩

section RowShape

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **A read-back clock is a genuine 24-bit low clock, and lands where the window says.** The two
`CPUState` byte checks bound `clk_low` below `2 ^ 24 - 6`, so adding any offset up to the syscall
width is exact natural-number addition — which is what makes `clk + 4/3/2` real access clocks
rather than field sums that might have wrapped. -/
theorem syscallRow_memPush_time (r : SyscallInstrsChip.Inputs (ZMod p))
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (idx : ZMod p) (v : Word (ZMod p)) (off : ℕ) (hoff : off ≤ 6)
    (c : ZMod p) (hc : ((off : ℕ) : ZMod p) = c) :
    MemoryMsg.timeNat (SyscallInstrsChip.memPushedMessage r idx c v)
        = StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + off ∧
      Channels.MemoryMsg.ClkBound (SyscallInstrsChip.memPushedMessage r idx c v) := by
  obtain ⟨lowSmall, addVal⟩ := TimeExtraction.clkVal_small_add_of_cpuState_bounds
    r.state.clk_0_16 r.state.clk_16_24 off (by omega) clk0B clk1B
  rw [← hc]
  constructor
  · show Semantics.clkNat r.state.clk_high
        (r.state.clk_0_16 + r.state.clk_16_24 * 65536 + ((off : ℕ) : ZMod p))
      = Semantics.clkNat r.state.clk_high (r.state.clk_0_16 + r.state.clk_16_24 * 65536) + off
    simp only [Semantics.clkNat]
    omega
  · show (r.state.clk_0_16 + r.state.clk_16_24 * 65536 + ((off : ℕ) : ZMod p)).val < 2 ^ 24
    omega

end RowShape

/-- **The syscall row's step fact**, at the event trajectory — the syscall analogue of
`stepFact_of_advance`, and the reason the walk had to be parameterized: its conclusion is
`LocalStateTruthG` at a trajectory whose step here is the handler, not `try_step`.

⚠ **The sketch's signature carried none of the linkage this needs**, which made it unprovable
rather than merely unproved. A payload alone says what *a* row does to *a* state; it says nothing
about *this* row sitting at *this* position of *this* transcript. Three hypotheses supply that, and
each is a real obligation on the caller rather than bookkeeping:

* `positioned` — wherever the row's State pull lands on the timeline, the transcript's event at that
  index *is* this row's syscall event. This is the row-to-transcript identification, and without it
  the trajectory's successor has no reason to be the handler's target.
* `rowContext` — the operand and carry facts hold at whatever state the pull observes. The Memory and
  Program buses supply these; naming them here keeps the step fact honest about what is not row-local.
* `clockAgrees` — the pushed clock really is `pull + 264`, the `StateBump` canonicalization premise
  that `syscallRowOKCore` also takes.

The ordinary analogue hides all three inside `RowWiring`. A syscall `RowWiring` is the natural next
step; until it exists these are the fields it would have. -/
theorem syscallStepFact_of_advance [Fact (2 ^ 25 < p)]
    (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (r : SyscallInstrsChip.Inputs (ZMod p))
    (payload : SyscallAdvancePayload (p := p) handler)
    (real : r.is_real = 1) (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (canonical : (syscallEventOfRow r).IsInlineCanonical)
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (u64A : Word.isU64 r.op_a_value)
    (opA : ((5 : ℕ) : ZMod p) = r.op_a)
    (positioned : ∀ n : ℕ,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)
        = (eventTimeline events initialClock).start n →
      events[n]? = some (ExecutionEvent.syscall (syscallEventOfRow r)))
    (rowContext : ∀ (n : ℕ) (s : SailState),
      eventTrajectory handler prog events initial n = some s →
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)
        = (eventTimeline events initialClock).start n →
      SyscallRowContext r prog s)
    (clockAgrees : StateMsg.timeNat (SyscallInstrsChip.statePushedMessage r)
      = StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 264) :
    LocalStepFactG prog (eventTrajectory handler prog events initial) initial
      (eventTimeline events initialClock) (syscallRowFacts r) := by
  intro hpull hcurr
  obtain ⟨n, state, htraj, htime, hpc, hrom, hcfg⟩ := hpull
  have htime' : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)
      = (eventTimeline events initialClock).start n := htime
  have hev := positioned n htime'
  obtain ⟨s', htrans, heff⟩ :=
    payload r prog state real spec sel pulled canonical hcfg hrom (rowContext n state htraj htime')
  set tl := eventTimeline events initialClock with tlDef
  have hdur : Semantics.durationAt events n = 264 := by simp [Semantics.durationAt, hev]
  have hstartSucc : tl.start (n + 1) = tl.start n + 264 := by
    rw [tlDef, eventTimeline_start_succ, hdur]
  -- the trajectory's own successor *is* the handler's target, because `events[n]` is this row
  have hsucc : eventTrajectory handler prog events initial (n + 1) = some s' := by
    rw [Semantics.eventTrajectory_succ, hev]
    dsimp only
    rw [htraj, Option.bind_some]
    exact htrans.2.2
  -- the row's three touch clocks and their `ClkBound`s
  obtain ⟨timeA, boundA⟩ := syscallRow_memPush_time r clk0B clk1B r.op_a r.op_a_value 4
    (by norm_num) 4 (by norm_num)
  obtain ⟨timeB, boundB⟩ := syscallRow_memPush_time r clk0B clk1B r.op_b
    r.op_b_memory.prev_value 3 (by norm_num) 3 (by norm_num)
  obtain ⟨timeC, boundC⟩ := syscallRow_memPush_time r clk0B clk1B r.op_c
    r.op_c_memory.prev_value 2 (by norm_num) 2 (by norm_num)
  obtain ⟨locPullA, locPushA⟩ := syscallRow_locOf_reg r (i := 5#5) opA r.op_a_memory
    r.op_a_value 4
  -- the currency antecedent, at the row's three pulls
  have currB := hcurr (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b,
    StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 3) (by simp [syscallRowFacts])
  have currC := hcurr (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c,
    StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 2) (by simp [syscallRowFacts])
  refine ⟨⟨n + 1, s', hsucc, ?_, heff.pc, ?_, heff.cfg hcfg⟩, ?_⟩
  · -- the pushed clock is the next timeline start, because this row's window is its event's duration
    show StateMsg.timeNat (SyscallInstrsChip.statePushedMessage r) = tl.start (n + 1)
    rw [hstartSucc, clockAgrees, htime']
  · -- ROM survives because a syscall row touches no memory
    intro a w hw i
    rw [heff.mem]
    exact hrom a w hw i
  · -- **The three read-backs.** `op_b`/`op_c` are pure reads: their pushes carry the pulled word at
    -- the pulled location and the pulled read time, so their truth *is* the currency antecedent's.
    -- `op_a` is the write, and it is the one that needs the post-state — which is why its push sits
    -- at `t + 4`, on or after `regEffectOffset`.
    intro message messageMem
    simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at messageMem
    rcases messageMem with rfl | rfl | rfl
    · refine ⟨u64A, boundA, ?_⟩
      have hstart0 : tl.start 0 ≤ tl.start n := tl.start_le_of_le (Nat.zero_le n)
      have hstep : tl.stepOf (tl.start n + 4) = n :=
        tl.stepOf_eq (by omega) (by rw [hstartSucc]; omega)
      have htimeA : Semantics.MemoryMsg.timeNat
          (SyscallInstrsChip.memPushedMessage r r.op_a 4 r.op_a_value) = tl.start n + 4 := by
        rw [timeA, htime']
      show Semantics.microValueG (eventTrajectory handler prog events initial) initial tl
        (Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPushedMessage r r.op_a 4 r.op_a_value))
        (Semantics.MemoryMsg.timeNat
          (SyscallInstrsChip.memPushedMessage r r.op_a 4 r.op_a_value))
        = some (Word.toBitVec64 r.op_a_value)
      rw [locPushA, htimeA]
      simp only [Semantics.microValueG, if_neg (by omega : ¬ tl.start n + 4 < tl.start 0),
        hstep, Nat.add_sub_cancel_left, Semantics.regEffectOffset, le_refl, decide_true,
        if_true, hsucc, Option.bind_some, Semantics.locContent]
      rw [heff.t0, result_syscallEventOfRow]
      rfl
    · refine ⟨currB.1, boundB, ?_⟩
      rw [timeB]
      exact currB.2.2
    · refine ⟨currC.1, boundC, ?_⟩
      rw [timeC]
      exact currC.2.2

omit [Fact (2 ^ 17 < p)] in
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
theorem syscallRowOKCore [Fact (2 ^ 25 < p)] (initialClock : ℕ)
    (r : SyscallInstrsChip.Inputs (ZMod p)) (real : r.is_real = 1)
    (spec : SyscallInstrsChip.Spec r)
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (opA : ((5 : ℕ) : ZMod p) = r.op_a) (opB : ((10 : ℕ) : ZMod p) = r.op_b)
    (opC : ((11 : ℕ) : ZMod p) = r.op_c)
    (align : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) % 8 = initialClock % 8)
    (canonicalClock : StateMsg.timeNat (SyscallInstrsChip.statePushedMessage r)
      = StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 264) :
    TimedGrounding.RowOKCore initialClock (syscallRowFacts r) := by
  set t := StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) with tDef
  obtain ⟨locPullA, locPushA⟩ := syscallRow_locOf_reg r (i := 5#5) opA r.op_a_memory
    r.op_a_value 4
  obtain ⟨locPullB, locPushB⟩ := syscallRow_locOf_reg r (i := 10#5) opB r.op_b_memory
    r.op_b_memory.prev_value 3
  obtain ⟨locPullC, locPushC⟩ := syscallRow_locOf_reg r (i := 11#5) opC r.op_c_memory
    r.op_c_memory.prev_value 2
  obtain ⟨timeA, boundA⟩ := syscallRow_memPush_time r clk0B clk1B r.op_a r.op_a_value 4
    (by norm_num) 4 (by norm_num)
  obtain ⟨timeB, boundB⟩ := syscallRow_memPush_time r clk0B clk1B r.op_b
    r.op_b_memory.prev_value 3 (by norm_num) 3 (by norm_num)
  obtain ⟨timeC, boundC⟩ := syscallRow_memPush_time r clk0B clk1B r.op_c
    r.op_c_memory.prev_value 2 (by norm_num) 2 (by norm_num)
  refine
    { timeGap := ?_
      align8 := align
      touches := ?_
      chain_mono := ?_
      pushClkBound := ?_
      slotOfClkBound := ?_ }
  · show t + 8 ≤ StateMsg.timeNat (SyscallInstrsChip.statePushedMessage r)
    omega
  · refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
    · exact ⟨locPushA.trans locPullA.symm, le_rfl, Nat.le_add_right _ _,
        Or.inr (by rw [timeA, locPushA]; rfl)⟩
    · exact ⟨locPushB.trans locPullB.symm, Nat.le_add_right _ _,
        by rw [locPullB]; simp [syscallRowFacts], Or.inl ⟨rfl, timeB⟩⟩
    · exact ⟨locPushC.trans locPullC.symm, Nat.le_add_right _ _,
        by rw [locPullC]; simp [syscallRowFacts], Or.inl ⟨rfl, timeC⟩⟩
  · -- Each location carries at most one of the row's three touches, because `x5`/`x10`/`x11` are
    -- distinct — which is exactly why the operand indices had to be pinned. With `op_a = op_b` the
    -- chain would demand `t + 4 < t + 3`.
    intro loc
    rcases eq_or_ne loc (Semantics.MemLoc.reg 5#5) with rfl | n5
    · simp [TimedGrounding.rowTouchesAt, syscallRowFacts, locPushA, locPushB, locPushC]
    rcases eq_or_ne loc (Semantics.MemLoc.reg 10#5) with rfl | n10
    · simp [TimedGrounding.rowTouchesAt, syscallRowFacts, locPushA, locPushB, locPushC]
    rcases eq_or_ne loc (Semantics.MemLoc.reg 11#5) with rfl | n11
    · simp [TimedGrounding.rowTouchesAt, syscallRowFacts, locPushA, locPushB, locPushC]
    · simp [TimedGrounding.rowTouchesAt, syscallRowFacts, locPushA, locPushB, locPushC,
        Ne.symm n5, Ne.symm n10, Ne.symm n11]
  · intro m mMem
    simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at mMem
    rcases mMem with rfl | rfl | rfl
    exacts [boundA, boundB, boundC]
  · intro pq pqMem prevBound
    simp only [syscallRowFacts, List.zip_cons_cons, List.zip_nil_right,
      List.mem_cons, List.not_mem_nil, or_false] at pqMem
    rcases pqMem with rfl | rfl | rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_registerAccessCols _ _ r.op_a_memory r.is_real
        (SyscallInstrsChip.clkLow r + 4) real prevBound spec.2.2.1 rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_registerAccessCols _ _ r.op_b_memory r.is_real
        (SyscallInstrsChip.clkLow r + 3) real prevBound spec.2.2.2.1 rfl rfl rfl
    · exact TimeExtraction.memoryTimeNat_lt_of_registerAccessCols _ _ r.op_c_memory r.is_real
        (SyscallInstrsChip.clkLow r + 2) real prevBound spec.2.2.2.2.1 rfl rfl rfl

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

/-- The two clock limbs recombine without wrapping — **and this genuinely needs `2 ^ 24 < p`**, not
the ambient `2 ^ 17 < p`. The recombined low clock reaches `2 ^ 24`, so on a smaller field the field
addition wraps and the equation is false. `clkBound_of_cpuState_bounds` takes the same split; the
difference is that it can *dodge* the small-field case (every value is then `< 2 ^ 24` outright),
while an equation between the decoded clock and the message's clock cannot. -/
private theorem clkLow_val {clk0 clk1 : ZMod p} (hp24 : 2 ^ 24 < p)
    (clk0Bound : ((clk0 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1Bound : clk1.val < 2 ^ 8) :
    (clk0 + clk1 * 65536).val = clk0.val + clk1.val * 65536 := by
  have h17 := Fact.out (p := 2 ^ 17 < p)
  set scaled := (clk0 - 1) * (8 : ZMod p)⁻¹ with scaledDef
  have reconstruct : scaled * 8 + 1 = clk0 := by
    rw [scaledDef, mul_assoc, inv_mul_cancel₀ SP1Clean.val_8_ne_zero, mul_one,
      sub_add_cancel]
  have scaledMulVal : (scaled * 8).val = scaled.val * 8 := by
    rw [ZMod.val_mul_of_lt (by rw [SP1Clean.val_8_zmod_p]; omega),
      SP1Clean.val_8_zmod_p]
  have clk0Val : clk0.val = scaled.val * 8 + 1 := by
    rw [← reconstruct, ZMod.val_add_of_lt (by rw [scaledMulVal, ZMod.val_one]; omega),
      scaledMulVal, ZMod.val_one]
  have highLimbVal : (clk1 * 65536).val = clk1.val * 65536 := by
    rw [ZMod.val_mul_of_lt (by rw [SP1Clean.val_65536_zmod_p]; omega),
      SP1Clean.val_65536_zmod_p]
  rw [ZMod.val_add_of_lt (by rw [highLimbVal]; omega), highLimbVal]

/-- **The clock coupling**: a syscall row's event carries the very clock its State pull sits at,
which is what `EventTransitionsClocked` demands and what an ordinary row gets for free.

This is the first place the *semantic* transcript clock and the *bus* clock the trail walks are
forced to be the same number, and the sketch stated it as though that were definitional. It is not.
The decoder reads three separate limbs (`clk_high`, `clk_16_24`, `clk_0_16`) while the pulled message
carries the two low ones already recombined as `clk_0_16 + clk_16_24 * 65536`, so the two agree only
once that field addition is known not to wrap — hence the row's `Spec`, for the limb bounds, and the
concrete field bound. `SyscallTrail` already runs at `Fact (2 ^ 24 < p)`, so this is the layer where
that stronger assumption first earns its place rather than a new demand. -/
theorem syscallEvent_startsAt (r : SyscallInstrsChip.Inputs (ZMod p)) (hp24 : 2 ^ 24 < p)
    (spec : SyscallInstrsChip.Spec r) (real : r.is_real = 1) :
    (ExecutionEvent.syscall (syscallEventOfRow r)).StartsAt
      (StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r)) := by
  obtain ⟨hlow, hhigh⟩ : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
      ∧ (r.state.clk_16_24).val < 2 ^ 8 := spec.2.1 real
  show (r.state.clk_high).val * 2 ^ 24 + (r.state.clk_16_24).val * 2 ^ 16 + (r.state.clk_0_16).val
      = (r.state.clk_high).val * 2 ^ 24 + (r.state.clk_0_16 + r.state.clk_16_24 * 65536).val
  rw [clkLow_val hp24 hlow hhigh]
  ring

end SP1Clean.Soundness
