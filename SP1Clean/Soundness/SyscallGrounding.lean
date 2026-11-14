import SP1Clean.Soundness.SyscallRowSemantics
import SP1Clean.Soundness.GenericWalk
import SP1Clean.Soundness.GroundingAdapter

/-! # Ordinary and syscall row facts on one trajectory

An ordinary row's step and frame facts are stated over the shard's trajectory, so they hold on
shards that also contain host calls. `RowWiring.advance_at` reads the row's currency only through
`localValueAt_stepStart_iff`, to obtain the operand bounds the chip's `advance` needs.

A syscall row's message facts (`syscallRowFacts`: its State pull and push, its fetch, and its
register pulls and pushes at offsets 4/3/2) and its start clock (`syscallEvent_startsAt`) are what
host-call grounding consumes. Its effect comes from the concrete host interpreter, not from Sail's
`try_step`. Every duration is a multiple of eight (`264 = 8·33`), so a host call leaves every later
row's `align8` residue unchanged. -/

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

/-! ## The duration generalizations

Three statements in the engine were pinned to exactly eight ticks; all three now have a
duration-generic form. `clockCount_of_stateWalk_durations` and
`statePullTime_of_stateWalk_durations` were already generic — only their `+8` wrappers were being
used — and `statePullAlign8_of_durations` joins them in `GenericWalk.lean`, beside the two lemmas
its proof consumes. -/

/-! ## The transcript

Building the event list from the ordered rows is what ties the semantic clock to the bus clock. -/

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
