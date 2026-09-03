import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Semantics.EventTime

/-! # What the ensemble certifies, when a shard can also make a syscall

`SupportedCoreSailRelation` — the *conclusion* of `supported_core_native_sound` — says a shard is
either an ordinary normally-retiring `SailRetireChain` between the committed pc endpoints, or such a
prefix reaching a `SP1Halted` state parked at `haltPc`. Both arms are chains of `try_step`, and both
hard-code the clock as `8 * steps` (plus one `264` on the halting arm).

Neither can describe a shard that **commits**. A mid-shard `COMMIT` row is not a `try_step`, so no
`SailRetireChain` contains it, and the shard's clock is no longer eight times anything.

So the headline's conclusion has to generalize. The shape is **generalize and re-derive**, not
weaken: this file states the relation over event transcripts, and `SupportedCoreSailRelation` comes
back as its all-ordinary specialization. That specialization is the honesty check on the whole
exercise — if the existing relation is not recoverable, the generalization is wrong.

Three changes ride along, each already justified against SP1:

* **The clock is a prefix sum** of the transcript's own durations rather than `8 * steps`, because
  the row at each index decides its own window width.
* **`OrdinaryRun` loses `exit_code = 0`** (D8). Upstream leaves `exit_code` free on a non-halting
  execution shard whose `prev_exit_code` is zero — it is sticky once set and chained across shards by
  the verifier, never pinned within one. The native "Exit hand-off forces zero" is a restriction SP1
  does not make.
* **The halting arm gains the canonicity premise** (D9), because `SP1Halted` wants the exact Rust
  `SyscallCode::HALT` in `t0` and the AIR only sees byte 0. -/

namespace SP1Clean.Execution

open LeanRV64D.Defs
open Sail LeanRV64D
open SP1Clean.Soundness.Target
open SP1Clean.Semantics

/-- One shard segment, as an event transcript rather than a step count. The transcript replaces
`SailSegmentWitness.steps`: its length is the step count, and its durations are the clock. -/
structure EventSegmentWitness where
  initial : SailState
  events : List Machine.ExecutionEvent
  final : SailState
  memory : Machine.CoreMemoryBoundary

/-- The clock the transcript spans: each event's own window width, summed. On an all-ordinary
transcript this is `8 * events.length`, which is where the existing statements' arithmetic comes
from. -/
def EventSegmentWitness.elapsed (w : EventSegmentWitness) : ℕ :=
  (w.events.map Machine.ExecutionEvent.duration).sum

/-- Every ordinary step of the transcript retires normally — the event-chain analogue of
`SailRetireChain`'s per-step condition. Syscall steps are excluded because the handler, not
`try_step`, moves the machine there. -/
def EventSegmentWitness.OrdinaryStepsRetire (handler : Machine.ExecutableSyscallHandler)
    (program : GuestProgram) (w : EventSegmentWitness) : Prop :=
  ∀ n : ℕ, ∀ s s' : SailState,
    w.events[n]? = some Machine.ExecutionEvent.ordinary →
    eventTrajectory handler program w.events w.initial n = some s →
    eventTrajectory handler program w.events w.initial (n + 1) = some s' →
    SailRetiresNormally s s'

/-- **The canonicity premise (D9)**, at the segment level: every syscall the transcript takes uses
one of the thirteen inline codes exactly. True of any execution SP1's executor produces — it panics
otherwise — and checkable on the witness. -/
def EventSegmentWitness.CanonicalSyscallCodes (w : EventSegmentWitness) : Prop :=
  ∀ event ∈ w.events, ∀ e : Machine.CoreSyscallEvent,
    event = Machine.ExecutionEvent.syscall e → e.IsInlineCanonical

/-- **The ordinary run shape**, generalized. The transcript reaches the committed final pc in its own
elapsed time. Note what is *absent* relative to `SailSegmentWitness.OrdinaryRun`: no `exit_code = 0`,
because SP1 does not constrain it here (D8). -/
def EventSegmentWitness.OrdinaryRun {p : ℕ} (handler : Machine.ExecutableSyscallHandler)
    (statement : SupportedCoreStatement p) (w : EventSegmentWitness) : Prop :=
  eventTrajectory handler statement.program w.events w.initial w.events.length = some w.final ∧
  w.OrdinaryStepsRetire handler statement.program ∧
  w.final.regs.get? Register.PC = some statement.finalPcBits ∧
  statement.finalClkNat = statement.initClkNat + w.elapsed

/-- **The halting run shape**, generalized. The transcript's last event is the halting syscall; the
state before it is genuinely `SP1Halted`, and the final state is that state parked at `haltPc`. The
`264` is now just the last event's own duration, so it is not a special case any more. -/
def EventSegmentWitness.HaltedRun {p : ℕ} (handler : Machine.ExecutableSyscallHandler)
    (statement : SupportedCoreStatement p) (w : EventSegmentWitness) : Prop :=
  ∃ preHalt : SailState,
    1 ≤ w.events.length ∧
    eventTrajectory handler statement.program w.events w.initial (w.events.length - 1)
      = some preHalt ∧
    w.OrdinaryStepsRetire handler statement.program ∧
    SP1Halted statement.program statement.exitCodeBits preHalt ∧
    w.final = { preHalt with regs := preHalt.regs.insert Register.PC Machine.haltPc } ∧
    statement.finalPcBits = Machine.haltPc ∧
    statement.finalClkNat = statement.initClkNat + w.elapsed

/-- **The event relation.** What the native ensemble certifies about the official machine once a
shard may also make a syscall: from the committed start, the transcript either runs to the committed
final pc or halts, with the Memory boundary well formed at the committed final clock and agreeing
with real content at both ends. -/
def SupportedCoreEventRelation {p : ℕ} (handler : Machine.ExecutableSyscallHandler) :
    WitnessRelation.Relation (SupportedCoreStatement p) EventSegmentWitness :=
  fun statement w =>
    statement.program.WellFormed ∧
    ShardStartState statement w.initial ∧
    w.CanonicalSyscallCodes ∧
    w.memory.WellFormed statement.finalClkNat ∧
    w.memory.AgreesWith w.initial w.final ∧
    (EventSegmentWitness.OrdinaryRun handler statement w ∨
      EventSegmentWitness.HaltedRun handler statement w)

/-! ## The specialization

The honesty check: on an all-ordinary transcript the event relation *is* the plain-Sail relation.
If this cannot be proved, the generalization above has changed the claim rather than widened it. -/

/-- The `SailSegmentWitness` an all-ordinary transcript denotes. -/
def EventSegmentWitness.toSailSegment (w : EventSegmentWitness) : SailSegmentWitness :=
  { initial := w.initial, steps := w.events.length, final := w.final, memory := w.memory }

/-- **The bridge.** An all-ordinary transcript satisfying the event relation satisfies the existing
plain-Sail relation, with `elapsed` collapsing to `8 * steps` and `eventTrajectory` to
`SailRetireChain`. Modulo D8's dropped `exit_code = 0`, which is recovered from the ensemble's own
Exit accounting rather than from the run shape. -/
theorem supportedCoreSailRelation_of_event {p : ℕ} (handler : Machine.ExecutableSyscallHandler)
    (statement : SupportedCoreStatement p) (w : EventSegmentWitness)
    (ordinary : ∀ event ∈ w.events, event = Machine.ExecutionEvent.ordinary)
    (exitZero : statement.publicValues.exit_code = 0)
    (h : SupportedCoreEventRelation handler statement w) :
    SupportedCoreSailRelation statement w.toSailSegment := by
  -- SKETCH (L5): `eventTrajectory_allOrdinary` turns the trajectory into `Machine.trajectory`, whose
  -- defined values are `SailChain`s; `OrdinaryStepsRetire` upgrades each to `SailRetiresNormally`,
  -- giving `SailRetireChain`. `elapsed` is `8 * length` because every `durationAt` is `8`.
  sorry

/-- **The positional accessor `SailRetireChain` lacks.** The inductive exposes `toSailChain` and
`snoc` and nothing else, so a chain cannot be read at an index — yet `OrdinaryStepsRetire` is stated
*pointwise over the trajectory*. Bridging the two run shapes in either direction needs exactly this
lemma, and its absence is why neither specialization bridge was reachable. Local to this file during
the sketch phase; it belongs beside `SailRetireChain.toSailChain`. -/
theorem retiresAt_of_sailRetireChain : ∀ {n : ℕ} {a b : SailState}, SailRetireChain n a b →
    ∀ k, k < n → ∀ s s' : SailState,
      Machine.trajectory a k = some s → Machine.trajectory a (k + 1) = some s' →
      SailRetiresNormally s s' := by
  intro n a b chain
  induction chain with
  | refl s => intro k hk; omega
  | @step m x y z hstep rest ih =>
      have hstep1 : Machine.trajectory x 1 = some y := by
        obtain ⟨-, -, -, -, -, hrun⟩ := hstep
        simp [Machine.trajectory, Machine.stepOnce, hrun]
      have hshift : ∀ i : ℕ, Machine.trajectory x (i + 1) = Machine.trajectory y i := by
        intro i
        rw [Nat.add_comm i 1, Machine.trajectory_add, hstep1, Option.bind_some]
      intro k hk s s' hs hs'
      cases k with
      | zero =>
          have hsx : s = x := (Option.some.inj hs).symm
          have hsy : s' = y := by rw [hshift 0] at hs'; exact (Option.some.inj hs').symm
          subst hsx; subst hsy; exact hstep
      | succ j =>
          exact ih j (by omega) s s' (by rwa [hshift] at hs) (by rwa [hshift] at hs')

/-- Every event of a replicated all-ordinary transcript is ordinary. -/
private theorem mem_replicate_ordinary (n : ℕ) :
    ∀ event ∈ List.replicate n Machine.ExecutionEvent.ordinary,
      event = Machine.ExecutionEvent.ordinary :=
  fun _ h => List.eq_of_mem_replicate h

/-- An all-ordinary transcript's elapsed clock is the uniform `8 * steps`, which is where the
existing statements' arithmetic comes from. -/
theorem elapsed_of_allOrdinary (w : EventSegmentWitness)
    (ordinary : ∀ event ∈ w.events, event = Machine.ExecutionEvent.ordinary) :
    w.elapsed = 8 * w.events.length := by
  have hmap : w.events.map Machine.ExecutionEvent.duration
      = List.replicate w.events.length 8 := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    rw [ordinary e he]
    rfl
  rw [EventSegmentWitness.elapsed, hmap, List.sum_replicate]
  simp [Nat.mul_comm]

private theorem elapsed_replicate (n : ℕ) (initial final : SailState)
    (memory : Machine.CoreMemoryBoundary) :
    EventSegmentWitness.elapsed
        ⟨initial, List.replicate n Machine.ExecutionEvent.ordinary, final, memory⟩
      = 8 * n := by
  rw [elapsed_of_allOrdinary _ (mem_replicate_ordinary n)]
  simp

/-- **The converse direction, on the ordinary arm.** Every plain-Sail witness of a non-halting shard
is an all-ordinary event witness denoting the same segment — which is what keeps the generalization
from being a *different* claim rather than a wider one. -/
theorem event_of_ordinaryRun {p : ℕ} (handler : Machine.ExecutableSyscallHandler)
    (statement : SupportedCoreStatement p) (w : SailSegmentWitness)
    (h : SupportedCoreSailRelation statement w)
    (run : SailSegmentWitness.OrdinaryRun statement w) :
    ∃ w' : EventSegmentWitness,
      (∀ event ∈ w'.events, event = Machine.ExecutionEvent.ordinary) ∧
      w'.toSailSegment = w ∧
      SupportedCoreEventRelation handler statement w' := by
  obtain ⟨wellFormed, start, memWF, memAgrees, -⟩ := h
  obtain ⟨chain, finalPc, clock, -⟩ := run
  refine ⟨⟨w.initial, List.replicate w.steps Machine.ExecutionEvent.ordinary, w.final, w.memory⟩,
    mem_replicate_ordinary _, ?_, ?_⟩
  · simp [EventSegmentWitness.toSailSegment]
  · -- the transcript denotes the very same run, step for step
    have hord := mem_replicate_ordinary w.steps
    have hlen : (List.replicate w.steps Machine.ExecutionEvent.ordinary).length = w.steps :=
      List.length_replicate
    have htraj : ∀ n ≤ w.steps,
        eventTrajectory handler statement.program
            (List.replicate w.steps Machine.ExecutionEvent.ordinary) w.initial n
          = Machine.trajectory w.initial n := by
      intro n hn
      exact eventTrajectory_allOrdinary handler statement.program _ w.initial hord n (by omega)
    have hfinal : Machine.trajectory w.initial w.steps = some w.final :=
      chainState_of_sailChain chain.toSailChain
    refine ⟨wellFormed, start, ?_, memWF, memAgrees, Or.inl ⟨?_, ?_, finalPc, ?_⟩⟩
    · intro event hmem e heq
      rw [hord event hmem] at heq
      exact Machine.ExecutionEvent.noConfusion heq
    · rw [hlen, htraj _ (le_refl _)]; exact hfinal
    · intro n s s' hevent hn hn1
      dsimp only at hevent hn hn1
      have hlt : n < w.steps := by
        by_contra hcon
        rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hevent
        simp at hevent
      rw [htraj n (by omega)] at hn
      rw [htraj (n + 1) (by omega)] at hn1
      exact retiresAt_of_sailRetireChain chain n hlt s s' hn hn1
    · rw [elapsed_replicate]; exact clock

/-- **Why the converse bridge cannot be all-ordinary on the halting arm**, stated rather than left
as a remark, because it is the reason `event_of_ordinaryRun` above is restricted.

A halting Sail witness spends `8 * (steps - 1) + 264` ticks; an all-ordinary transcript of the same
length spends `8 * steps`. Those are equal only if `8 = 264`. So a halting shard's event transcript
*necessarily* contains a syscall event — which is not a defect of the bridge but the entire content
of the generalization: the 264-tick window is the thing `SailRetireChain` could never express, and
the event relation exists precisely to name it.

The consequence for the campaign is that the honest converse is arm-split, not uniform: `OrdinaryRun`
witnesses transfer verbatim, and `HaltedRun` witnesses transfer only once the halting syscall event
is constructed — which needs the handler, and so belongs with L6's live-halt-row witness rather than
here. -/
theorem no_allOrdinary_of_haltedRun {p : ℕ} (statement : SupportedCoreStatement p)
    (w : SailSegmentWitness) (w' : EventSegmentWitness)
    (halted : SailSegmentWitness.HaltedRun statement w)
    (hseg : w'.toSailSegment = w)
    (helapsed : statement.finalClkNat = statement.initClkNat + w'.elapsed)
    (ordinary : ∀ event ∈ w'.events, event = Machine.ExecutionEvent.ordinary) : False := by
  obtain ⟨preHalt, hpos, -, -, -, -, hclock⟩ := halted
  have hlen : w'.events.length = w.steps := by
    rw [← hseg]; rfl
  rw [elapsed_of_allOrdinary w' ordinary, hlen] at helapsed
  omega

end SP1Clean.Execution
