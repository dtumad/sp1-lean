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

open LeanRV64D

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A timeline's `start` is injective, because it strictly increases.  This is the identification
that turns "the walk reports *some* trajectory index" into "the walk reports *this* index", and it
is what keeps the engine's list position and the transcript's timeline position one number rather
than two that must be reconciled later.

It belongs beside `Timeline.start_lt_of_lt` in `Model/Semantics/MicroTime.lean`; it lives here to
avoid a rebuild of everything below that file, and is public because the mixed-row instantiation
consumes it. -/
theorem start_injective (tl : Semantics.Timeline) : Function.Injective tl.start := by
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
  rw [Std.ExtDHashMap.get?_insert, dite_eq_right hne]

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
  rw [Std.ExtDHashMap.get?_insert, dite_eq_right hnex5, Std.ExtDHashMap.get?_insert, dite_eq_right hnePC]

/-! ## The ordinary row's step fact

An instruction row's step fact is stated over the shard's trajectory, so it holds on shards that
also contain syscall rows. `RowWiring.advance_at` uses the row's currency only through
`localValueAt_stepStart_iff`, to obtain the operand bounds the chip's `advance` needs; `advance`
itself needs only the state. -/

/-- The chip's `advance` at row `n` of a trajectory, with the row's window starting at
`tl.start n`. -/
theorem RowWiring.advance_at {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    {traj : Semantics.Trajectory} {initial state : SailState} {tl : Semantics.Timeline} {n : ℕ}
    (htraj : traj n = some state)
    (htime : StateMsg.timeNat rf.statePull = tl.start n)
    (hpc : state.regs.get? Register.PC = some (StateMsg.pcBits rf.statePull))
    (hrom : RomLoaded program state) (hcfg : SailConfigured state)
    (curr : ∀ mp ∈ rf.memPulls, Channels.MemoryMsg.isU64 mp.1 ∧
      Semantics.LocalValueAt traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ s', SailStep state s' ∧ RowEffect program (kind.view inp cols) state s' := by
  have operands : ValueOperandsBound (kind.view inp cols) state := by
    constructor
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opB_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
    · intro index himm hidx
      obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opC_pull index himm hidx
      have hc := (curr mp hmp).2
      rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
      exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
  have sourceA : SourceAValueBound (kind.view inp cols) state := by
    intro index hidx
    obtain ⟨mp, hmp, hloc, hval⟩ := wiring.opA_pull index hidx
    have hc := (curr mp hmp).2
    rw [hloc, wiring.readTime mp hmp, htime, hval] at hc
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
  have pulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (curr mp hmp).2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
  rw [wiring.statePull_eq, pcBits_statePullOfView] at hpc
  exact advance inp cols data program state real spec hcfg hrom hpc operands decode
    (ready state operands sourceA pulls)

/-! ## Reading a step back out of the trajectory

`LocalStepFact` records only that the trajectory has a successor. The lemmas below recover the
ordinary chip's actual step when the trajectory's successor at a row is Sail's `stepOnce`. -/

/-- An ordinary chip's semantic step on a trajectory whose successor at this row is Sail's
`stepOnce`. The timeline supplies this row's eight-tick duration; other rows may have any duration.
The proof uses the registered `advance` payload and the actual Memory pulls and pushes. -/
theorem ordinaryStepFact_of_rowEffect {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    (trajectory : Trajectory) (initial : SailState) (tl : Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st → RowEffect program (kind.view inp cols) st nx →
        RomLoaded program st → RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    LocalStepFact program trajectory initial
      tl rf := by
  intro hpull hcurr
  obtain ⟨n, state, htraj, htime, hpc, hrom, hcfg⟩ := hpull
  have hstartSucc := timeStep n htime
  obtain ⟨s', hstep, heff⟩ := wiring.advance_at advance real spec decode ready htraj htime
    hpc hrom hcfg (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.2⟩)
  -- The selected trajectory agrees with Sail at this row's position.
  have hsucc : trajectory (n + 1) = some s' := by
    rw [step n htime, htraj, Option.bind_some]
    exact TimedGrounding.stepOnce_of_sailStep hstep
  have hpushTime : StateMsg.timeNat rf.statePush = tl.start (n + 1) := by
    rw [hstartSucc, wiring.time8, htime]
  have hpulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (hcurr mp hmp).2.2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
  refine ⟨⟨n + 1, s', hsucc, hpushTime, ?_, codeMemoryCompatible htraj heff hrom,
    heff.cfg hcfg⟩, ?_⟩
  · rw [wiring.statePush_eq]
    show s'.regs.get? Register.PC
      = some (StateMsg.pcBits (statePushOfView (kind.view inp cols)))
    rw [pcBits_statePushOfView]
    exact heff.pc
  · -- every pushed Memory record is true, window-locally
    intro m hm
    rcases wiring.push_classified m hm with
      ⟨mp, hmp, hloc, hval, hlo, hhi, hramSafe⟩ |
      ⟨hw, hu64, ⟨idx, hlocw, hidx⟩, hvalw, htw⟩ |
      ⟨hnw, mp, hmp, ⟨idx, hlocr⟩, hloc, hval, htr⟩ |
      ⟨_hnw, hu64, hloc, hzero, htimeZero⟩ |
      ⟨cell, hu64, hloc, htimeRam, hpost⟩
    · -- read-back inside the pre-effect region
      have hc := (hcurr mp hmp).2.2
      rw [wiring.readTime mp hmp] at hc
      have hu : Channels.MemoryMsg.isU64 m := by
        show Word.isU64 m.value
        rw [hval]
        exact (hcurr mp hmp).1
      refine ⟨hu, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, hval]
      rw [htime] at hc
      -- Registers shift freely inside the pre-write half; a RAM read-back either sits at the window
      -- start already, or reads the post-state — where `hramSafe` says this row wrote no cell.
      cases hlocmp : Semantics.MemoryMsg.locOf mp.1 with
      | reg i =>
        rw [hlocmp] at hc
        exact TimedGrounding.localValueAt_shift_reg (n := n)
          (Or.inl ⟨le_rfl, by omega, by omega, by omega⟩) hc
      | ram a =>
        rw [hlocmp] at hc
        by_cases heq : Semantics.MemoryMsg.timeNat m = tl.start n
        · rw [heq]; exact hc
        · unfold Semantics.LocalValueAt at hc ⊢
          rw [TimedGrounding.microValue_ram_pre (n := n) le_rfl (by omega), htraj,
            Option.bind_some] at hc
          rw [TimedGrounding.microValue_ram_post (n := n) (by omega)
            (by rw [hstartSucc]; omega), hsucc, Option.bind_some]
          rw [locContent_ram_congr (heff.mem.1 (hramSafe a (hloc.trans hlocmp))) a]
          exact hc
    · -- the `op_a` write, at the `+ 4` effect slot
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hlocw, hvalw, htw, htime]
      show Semantics.microValue _ _ _ (MemLoc.reg idx) (tl.start n + 4) = _
      rw [TimedGrounding.microValue_reg_post (n := n) le_rfl (by rw [hstartSucc]; omega), hsucc,
        Option.bind_some]
      have hregs := heff.regs
      rw [ite_eq_left hw] at hregs
      exact hregs.1 idx hidx
    · -- a non-writing row's `op_a` read-back at the `+ 4` slot
      have hlocmp : Semantics.MemoryMsg.locOf mp.1 = MemLoc.reg idx := hloc.symm.trans hlocr
      have hc := (hcurr mp hmp).2.2
      rw [wiring.readTime mp hmp, hlocmp, htime] at hc
      have hu : Channels.MemoryMsg.isU64 m := by
        show Word.isU64 m.value
        rw [hval]
        exact (hcurr mp hmp).1
      refine ⟨hu, wiring.push_clkBound m hm, ?_⟩
      rw [hlocr, hval, htr, htime]
      show Semantics.microValue _ _ _ (MemLoc.reg idx) (tl.start n + 4) = _
      rw [TimedGrounding.microValue_reg_post (n := n) le_rfl (by rw [hstartSucc]; omega), hsucc,
        Option.bind_some]
      have hregs := heff.regs
      rw [ite_eq_right (by simp [hnw])] at hregs
      show locContent s' (MemLoc.reg idx) = some (Word.toBitVec64 mp.1.value)
      rw [show locContent s' (MemLoc.reg idx) = s'.get_reg? idx from rfl, hregs idx]
      rwa [TimedGrounding.localValueAt_stepStart_iff htraj] at hc
    · -- the factored `rd = x0` destination push
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, htimeZero, htime]
      show Semantics.microValue _ _ _ (MemLoc.reg 0#5) (tl.start n + 4) = _
      rw [TimedGrounding.microValue_reg_post (n := n) le_rfl (by rw [hstartSucc]; omega), hsucc,
        Option.bind_some]
      simp [locContent, SailState.get_reg?, hzero]
    · -- a genuine RAM write at the `+ 1` effect slot
      refine ⟨hu64, wiring.push_clkBound m hm, ?_⟩
      rw [hloc, htimeRam, htime]
      show Semantics.microValue _ _ _ (MemLoc.ram cell) (tl.start n + 1) = _
      rw [TimedGrounding.microValue_ram_post (n := n) le_rfl (by rw [hstartSucc]; omega), hsucc,
        Option.bind_some]
      exact hpost heff hpulls

/-- The original trajectory-wide ROM contract specializes to the selected row's effect. -/
theorem ordinaryStepFact_of_advanceOnTrajectory {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    (trajectory : Trajectory) (initial : SailState) (tl : Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st → SailStep st nx →
        RomLoaded program st → RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    LocalStepFact program trajectory initial
      tl rf := by
  exact ordinaryStepFact_of_rowEffect wiring advance real spec decode ready trajectory initial tl
    (fun present effect => codeMemoryCompatible present effect.normal.sailStep) timeStep step

/-- The ordinary chip's register/RAM frame argument on an arbitrary mixed trajectory. Only
this row's successor equation and eight-tick duration are needed. -/
theorem ordinaryFrameFact_of_advanceOnTrajectory {kind : ChipKind p}
    {inp : kind.Inputs (ZMod p)} {cols : kind.Cols (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring (kind.view inp cols) rf) (advance : kind.AdvancePayload)
    {data : ProverData (ZMod p)} {program : GuestProgram}
    (real : (kind.view inp cols).is_real = 1)
    (spec : kind.chipSpec inp cols data)
    (decode : Target.decodedInROM program (programAccess (kind.view inp cols)).toRow)
    (ready : ∀ s : SailState, ValueOperandsBound (kind.view inp cols) s →
      SourceAValueBound (kind.view inp cols) s → MemoryPullsBound rf s →
        kind.advanceReady inp cols program s)
    (trajectory : Trajectory) (initial : SailState) (tl : Timeline)
    (timeStep : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : ∀ n, StateMsg.timeNat rf.statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    FrameFact program trajectory initial
      tl rf := by
  intro hpull hcurr loc v hpush hvalAt
  obtain ⟨n, state, htraj, htime, hpc, hrom, hcfg⟩ := hpull
  have hstartSucc := timeStep n htime
  obtain ⟨s', hstep, heff⟩ := wiring.advance_at advance real spec decode ready htraj htime
    hpc hrom hcfg (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.2⟩)
  have hsucc : trajectory (n + 1) = some s' := by
    rw [step n htime, htraj, Option.bind_some]
    exact TimedGrounding.stepOnce_of_sailStep hstep
  rw [htime] at hvalAt
  have hcontent : locContent state loc = some (Word.toBitVec64 v) :=
    (TimedGrounding.localValueAt_stepStart_iff htraj).mp hvalAt
  have hpulls : MemoryPullsBound rf state := by
    intro mp hmp
    have hc := (hcurr mp hmp).2.2
    rw [wiring.readTime mp hmp, htime] at hc
    exact (TimedGrounding.localValueAt_stepStart_iff htraj).mp hc
  have hpushTime : StateMsg.timeNat rf.statePush = tl.start (n + 1) := by
    rw [hstartSucc, wiring.time8, htime]
  rw [hpushTime]
  apply (TimedGrounding.localValueAt_stepStart_iff hsucc).mpr
  cases loc with
  | ram cell =>
    exact wiring.ram_frame heff hpulls cell v hpush hcontent
  | reg i =>
    show s'.get_reg? i = some (Word.toBitVec64 v)
    have hregs := heff.regs
    by_cases hw : (kind.view inp cols).commit.writesReg = true
    · rw [ite_eq_left hw] at hregs
      by_cases hop : (i.toNat : ZMod p) = (kind.view inp cols).adapter.op_a
      · obtain ⟨m, hm, hlocm, hvalm⟩ := wiring.write_push hw i hop
        have hveq : m.value = v := hpush m hm hlocm
        rw [hregs.1 i hop, ← hvalm, hveq]
      · rw [hregs.2 i hop]
        exact hcontent
    · rw [ite_eq_right hw] at hregs
      rw [hregs i]
      exact hcontent

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

omit [Fact (2 ^ 17 < p)] in
/-- The walk's currency antecedent, split at the row's three named pulls. Stated over an **abstract**
row so the three membership proofs are checked once here rather than re-unified against a 65-column
concrete row at every use site — the crossing rule from the campaign log. -/
theorem syscallRowFacts_currency_split (r : SyscallInstrsChip.Inputs (ZMod p))
    (currency : ∀ mp ∈ (syscallRowFacts r).memPulls,
      Channels.MemoryMsg.isU64 (mp : Channels.MemoryMsg (ZMod p) × ℕ).1 ∧
        Channels.MemoryMsg.ClkBound mp.1) :
    (Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a) ∧
        Channels.MemoryMsg.ClkBound
          (SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a)) ∧
      (Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b) ∧
        Channels.MemoryMsg.ClkBound
          (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b)) ∧
      (Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c) ∧
        Channels.MemoryMsg.ClkBound
          (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c)) :=
  ⟨currency _ (by rw [syscallRowFacts_memPulls]; exact List.mem_cons_self),
   currency _ (by rw [syscallRowFacts_memPulls]; exact List.mem_cons_of_mem _ List.mem_cons_self),
   currency _ (by
     rw [syscallRowFacts_memPulls]
     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

omit [Fact (2 ^ 17 < p)] in
/-- `PulledFacts` assembled from the three buses' named pieces, over an **abstract** row. The
assembly is trivial — it is a re-association of twelve conjuncts — but doing it at a concrete
65-column row makes the anonymous constructor's defeq checks blow the depth budget, so the crossing
happens once here where every argument is a variable. -/
theorem SyscallInstrsChip.pulledFacts_of_buses (r : SyscallInstrsChip.Inputs (ZMod p))
    (prog : Channels.ProgramMsg.RowSpec (SyscallInstrsChip.programMessage r))
    (curA : Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a) ∧
      Channels.MemoryMsg.ClkBound (SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a))
    (curB : Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b) ∧
      Channels.MemoryMsg.ClkBound (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b))
    (curC : Channels.MemoryMsg.isU64 (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c) ∧
      Channels.MemoryMsg.ClkBound (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c))
    (u64 : Word.isU64 r.op_a_value) :
    SyscallInstrsChip.PulledFacts r :=
  fun _ => ⟨prog.1, prog.2.1, prog.2.2.1, prog.2.2.2.1, prog.2.2.2.2,
    curA.1, curA.2, curB.1, curB.2, curC.1, curC.2, u64⟩

/-- Each of the row's six Memory records addresses a register, because the committed `ECALL` pins
the three operand columns. This is where `witness_syscallRow_ecallTruth` pays for itself: without
it `locOf` falls through to `.ram`, whose `readWindow = 0` and `writeOffset = 1` make the offset-3
read and the offset-4 write unrepresentable. -/
theorem syscallRow_locOf_reg (r : SyscallInstrsChip.Inputs (ZMod p))
    {idx : ZMod p} {i : BitVec 5} (hidx : ((i.toNat : ℕ) : ZMod p) = idx)
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (v : Word (ZMod p)) (c : ZMod p) :
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

Three statements in the engine were pinned to exactly eight ticks; all three now have a
duration-generic form. `clockCount_of_stateWalk_durations` and
`statePullTime_of_stateWalk_durations` were already generic — only their `+8` wrappers were being
used — and `statePullAlign8_of_durations` joins them in `GenericWalk.lean`, beside the two lemmas
its proof consumes. -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The transcript's timeline agrees with the walk's positions: a row at trail index `k` pulls at
`tl.start k` and pushes at `tl.start (k+1)`. This is `walk`'s timeline hypothesis, and the index is
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
the identity that lets the walk's positions be read off the timeline and vice versa. It holds arm for arm because `WalkedRow` and `ExecutionEvent` are the
same two-way split. -/
theorem durationAt_transcriptOf (data : ProverData (ZMod p)) (rows : List (WalkedRow p)) (k : ℕ)
    (hk : k < rows.length) :
    Semantics.durationAt (transcriptOf data rows) k = (rows[k]'hk).duration := by
  have hlen : k < (transcriptOf data rows).length := by simpa [transcriptOf] using hk
  rw [Semantics.durationAt, List.getElem?_eq_getElem hlen]
  simp only [transcriptOf, List.getElem_map]
  cases rows[k] <;> rfl

/-- **The walked row's `RowFacts`** — the carrier the engine consumes once a syscall row can sit in
the middle of the trail. This is the type change `SyscallTableInactive.noActiveRows` exists to avoid:
today's engine walks `List (DecodedInstructionRow p)`, and a 264-tick row cannot join that list under
any choice of facts.

The instruction arm takes its facts from a **parameter** rather than fixing `ordinaryRowFacts`,
because the engine does not walk the ordinary carrier: it walks the *aligned* one, related to the
ordinary carrier by `AlignsWith`. Fixing the ordinary form here would produce a carrier the engine
cannot actually feed. -/
noncomputable def WalkedRow.facts (g : DecodedInstructionRow p → Semantics.RowFacts p) :
    WalkedRow p → Semantics.RowFacts p
  | .instruction row => g row
  | .syscall r => syscallRowFacts r

@[simp] theorem WalkedRow.facts_instruction (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (row : DecodedInstructionRow p) :
    WalkedRow.facts g (.instruction row) = g row := rfl

@[simp] theorem WalkedRow.facts_syscall (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (r : SyscallInstrsChip.Inputs (ZMod p)) :
    WalkedRow.facts g (.syscall r) = syscallRowFacts r := rfl

/-- The event a walked row denotes, named rather than inlined so the two positional lemmas below
share one motive. -/
noncomputable def WalkedRow.event : WalkedRow p → ExecutionEvent
  | .instruction _ => .ordinary
  | .syscall r => .syscall (syscallEventOfRow r)

theorem transcriptOf_eq_map (data : ProverData (ZMod p)) (rows : List (WalkedRow p)) :
    transcriptOf data rows = rows.map WalkedRow.event := rfl

/-- A walked row's window is the duration its own event reports — the pointwise form of
`durationAt_transcriptOf`, which the clock accounting needs off-index. -/
@[simp] theorem WalkedRow.duration_event (row : WalkedRow p) :
    row.event.duration = row.duration := by
  cases row <;> rfl

/-- The transcript's event at an index is the row's own event, by construction. -/
theorem transcriptOf_getElem? (data : ProverData (ZMod p)) (rows : List (WalkedRow p)) (k : ℕ)
    (hk : k < rows.length) :
    (transcriptOf data rows)[k]? = some (rows[k]'hk).event := by
  rw [transcriptOf_eq_map, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

/-- **The positional linkage, from the walk order.** Both step facts take a `positioned`
hypothesis — the ordinary one to know its transcript slot is `.ordinary`, the syscall one to know
its slot carries *this* row's event — and both are the same fact: `Timeline.start` is strictly
increasing, so the index at which a row's pull time lands is unique, and at *its own* index the
transcript holds its own event by construction.

That is the whole content of "the semantic transcript clock and the bus clock are the same number":
it is bought once, by the walk order, and spent by every row. -/
theorem positioned_of_walkOrder (data : ProverData (ZMod p))
    (g : DecodedInstructionRow p → Semantics.RowFacts p) (rows : List (WalkedRow p))
    (initialClock k : ℕ) (hk : k < rows.length)
    (hpull : StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
      = (eventTimeline (transcriptOf data rows) initialClock).start k) :
    ∀ n : ℕ, StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
        = (eventTimeline (transcriptOf data rows) initialClock).start n →
      (transcriptOf data rows)[n]? = some (rows[k]'hk).event := by
  intro n hn
  have hnk : n = k := start_injective _ (hn.symm.trans hpull)
  subst hnk
  exact transcriptOf_getElem? data rows n hk

/-- The transcript's prefix-summed durations are the walk order's own prefix-summed widths. This is
the arithmetic that replaces `8 * k` once a shard can contain a 264-tick row, and it is exact rather
than approximate because `durationAt_transcriptOf` matches the transcript index for index. -/
theorem transcriptOf_prefixSum (data : ProverData (ZMod p)) (rows : List (WalkedRow p)) :
    ∀ k : ℕ, k ≤ rows.length →
      ((List.range k).map (Semantics.durationAt (transcriptOf data rows))).sum
        = ((rows.take k).map WalkedRow.duration).sum := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hklt : k < rows.length := by omega
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega),
        List.take_add_one, List.map_append, List.sum_append,
        List.getElem?_eq_getElem hklt]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Option.toList_some]
      rw [durationAt_transcriptOf data rows k hklt]

/-- **Each walked row's pull time is its own timeline start.** The State walk telescopes the row
widths — `statePullTime_of_stateWalk_durations`, which is why that lemma had to be generalized off
`DecodedInstructionRow` — and `transcriptOf_prefixSum` says the transcript reports the same sum.

Together with `positioned_of_walkOrder` this is the whole clock coupling: the bus clock a row is
walked at and the semantic clock its event starts at are the same number, derived rather than
assumed.

The walk's `edge` is a **parameter** rather than the row's own `statePull`/`statePush`, because the
trail is extracted over the *canonicalized* State messages (`trailCanonEdge`) while the row's facts
carry the raw ones. `timeAgree` is the bridge, and at the real call site it is `timeNat_canonState`
— a rewriting, not a new obligation. -/
theorem walkedRow_pullAt (data : ProverData (ZMod p))
    (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p)) (initialClock : ℕ) {initialMsg finalMsg : StateMsg (ZMod p)}
    (edge : WalkedRow p → StateMsg (ZMod p) × StateMsg (ZMod p))
    (walk : Walk.IsWalk edge initialMsg finalMsg rows)
    (steps : ∀ r ∈ rows,
      StateMsg.timeNat (edge r).2 = StateMsg.timeNat (edge r).1 + r.duration)
    (timeAgree : ∀ r ∈ rows,
      StateMsg.timeNat (edge r).1 = StateMsg.timeNat (WalkedRow.facts g r).statePull)
    (headTime : StateMsg.timeNat initialMsg = initialClock)
    (k : ℕ) (hk : k < rows.length) :
    StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
      = (Semantics.eventTimeline (transcriptOf data rows) initialClock).start k := by
  have hsplit : rows = rows.take k ++ (rows[k]'hk) :: rows.drop (k + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have position := statePullTime_of_stateWalk_durations edge WalkedRow.duration walk steps
    (rows.take k) (rows[k]'hk) (rows.drop (k + 1)) hsplit
  rw [Semantics.eventTimeline_start, transcriptOf_prefixSum data rows k (by omega), ← headTime,
    ← timeAgree _ (List.getElem_mem hk)]
  exact position

omit [Fact (2 ^ 17 < p)] in
/-- **`SyscallRowContext` from its four named pieces, over an abstract row.** The assembly is a
re-association plus three `rfl`-level spelling changes — the event's `pc`/`rawCode`/`arg1`/`arg2`
*are* the row's recombined limbs — but at the witness's concrete 65-column row those `rfl`s exceed
the depth budget, so the crossing happens once here where every argument is a variable. -/
theorem SyscallRowContext.of_pieces (r : SyscallInstrsChip.Inputs (ZMod p))
    (prog : Target.GuestProgram) (source : SailState)
    (opA : ((5 : ℕ) : ZMod p) = r.op_a) (opB : ((10 : ℕ) : ZMod p) = r.op_b)
    (opC : ((11 : ℕ) : ZMod p) = r.op_c)
    (fetch : prog.fetchWord (Target.pcBitsOfRow
      (Semantics.rowOfMsg (SyscallInstrsChip.programMessage r))) = some Target.ECALL_ENC)
    (pcValue : source.regs.get? Register.PC
      = some (Semantics.pcBits (SyscallInstrsChip.statePulledMessage r).pc0
          (SyscallInstrsChip.statePulledMessage r).pc1
          (SyscallInstrsChip.statePulledMessage r).pc2))
    (vA : source.get_reg? 5#5 = some (Word.toBitVec64 r.op_a_memory.prev_value))
    (vB : source.get_reg? 10#5 = some (Word.toBitVec64 r.op_b_memory.prev_value))
    (vC : source.get_reg? 11#5 = some (Word.toBitVec64 r.op_c_memory.prev_value)) :
    SyscallRowContext r prog source :=
  ⟨⟨by simpa using opA.symm, by simpa using opB.symm, by simpa using opC.symm⟩,
   ⟨(syscallEventOfRow r).pc, pcValue, fetch⟩, ⟨vA, vB, vC⟩, pcValue⟩

omit [Fact (2 ^ 17 < p)] in
/-- The walk's *value* currency, split at the row's three named pulls — the `LocalValueAt` twin of
`syscallRowFacts_currency_split`, over an abstract row for the same crossing reason. -/
theorem syscallRowFacts_currency_split_values (r : SyscallInstrsChip.Inputs (ZMod p))
    {traj : Semantics.Trajectory} {initial : SailState} {tl : Semantics.Timeline}
    (hcurr : ∀ mp ∈ (syscallRowFacts r).memPulls,
      Semantics.LocalValueAt traj initial tl
        (Semantics.MemoryMsg.locOf (mp : Channels.MemoryMsg (ZMod p) × ℕ).1) mp.2 mp.1.value) :
    Semantics.LocalValueAt traj initial tl
        (Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPulledMessage r r.op_a_memory r.op_a))
        (StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r))
        r.op_a_memory.prev_value ∧
      Semantics.LocalValueAt traj initial tl
        (Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPulledMessage r r.op_b_memory r.op_b))
        (StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 3)
        r.op_b_memory.prev_value ∧
      Semantics.LocalValueAt traj initial tl
        (Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPulledMessage r r.op_c_memory r.op_c))
        (StateMsg.timeNat (SyscallInstrsChip.statePulledMessage r) + 2)
        r.op_c_memory.prev_value :=
  ⟨hcurr _ (by rw [syscallRowFacts_memPulls]; exact List.mem_cons_self),
   hcurr _ (by rw [syscallRowFacts_memPulls]; exact List.mem_cons_of_mem _ List.mem_cons_self),
   hcurr _ (by
     rw [syscallRowFacts_memPulls]
     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- **The successor to `listAllInl`.** Today's projection is what
`SyscallTableInactive.noActiveRows` exists to make available: with no syscall rows every trail entry
is a `Sum.inl`, so the trail *is* a list of decoded instruction rows and the engine can walk it.

This one asks only that no **halt** row is present — which the halt-free branch already establishes
from `realHaltRows witness = []` — and produces a `WalkedRow` list in the same order, so a syscall
row is carried through the projection rather than excluded by it.

The result is a `List.Forall₂` rather than a `List.map`: the two row types are related by a
*relation* (the syscall arm decodes a raw array), not by a function into `WalkedRow`, so there is no
map to speak of. `Walk.isWalk_forall₂` is the transport that shape needs. -/
theorem listAllWalked {α β γ : Type*} (dec : β → SyscallInstrsChip.Inputs (ZMod p))
    (mk : α → DecodedInstructionRow p) :
    ∀ (l : List (α ⊕ γ ⊕ β)),
      (∀ t ∈ l, (∃ a : α, t = Sum.inl a) ∨ (∃ b : β, t = Sum.inr (Sum.inr b))) →
      ∃ rows : List (WalkedRow p), List.Forall₂
        (fun t r => (∃ a : α, t = Sum.inl a ∧ r = WalkedRow.instruction (mk a)) ∨
          (∃ b : β, t = Sum.inr (Sum.inr b) ∧ r = WalkedRow.syscall (dec b))) l rows
  | [], _ => ⟨[], List.Forall₂.nil⟩
  | t :: l, hall => by
      obtain ⟨rows, hrows⟩ := listAllWalked dec mk l fun t ht => hall t (List.mem_cons_of_mem _ ht)
      rcases hall t List.mem_cons_self with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact ⟨WalkedRow.instruction (mk a) :: rows,
          List.Forall₂.cons (Or.inl ⟨a, rfl, rfl⟩) hrows⟩
      · exact ⟨WalkedRow.syscall (dec b) :: rows,
          List.Forall₂.cons (Or.inr ⟨b, rfl, rfl⟩) hrows⟩

/-- **The walk's timeline hypothesis, from the walk order.** The walk needs each row's push to land
on the *next* timeline start; the row supplies its own window width, and `durationAt_transcriptOf`
says the transcript reports exactly that width at the row's index. The two then agree by
`timelineAgreement_of_durations`.

This is where a mixed shard's arithmetic stops being `8 * k` and becomes a prefix sum, and it is
also where the `.bump` arm of `SyscallTrailRow` would break the identity — `WalkedRow` has no
zero-width arm, which is why the trail must be projected onto it before the walk begins. -/
theorem walkedRow_timeStep (data : ProverData (ZMod p))
    (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p)) (initialClock k : ℕ) (hk : k < rows.length)
    (hpull : StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
      = (eventTimeline (transcriptOf data rows) initialClock).start k)
    (hwidth : StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePush
      = StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
        + (rows[k]'hk).duration) :
    ∀ n : ℕ, StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
        = (eventTimeline (transcriptOf data rows) initialClock).start n →
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePush
        = (eventTimeline (transcriptOf data rows) initialClock).start (n + 1) :=
  timelineAgreement_of_durations _ initialClock _ k hpull
    (by rw [hwidth, durationAt_transcriptOf data rows k hk])

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
