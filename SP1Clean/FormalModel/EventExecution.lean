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

/-- The converse direction, which is what keeps the generalization from being a *different* claim:
every plain-Sail witness is an all-ordinary event witness. -/
theorem event_of_supportedCoreSailRelation {p : ℕ} (handler : Machine.ExecutableSyscallHandler)
    (statement : SupportedCoreStatement p) (w : SailSegmentWitness)
    (h : SupportedCoreSailRelation statement w) :
    ∃ w' : EventSegmentWitness,
      (∀ event ∈ w'.events, event = Machine.ExecutionEvent.ordinary) ∧
      w'.toSailSegment = w ∧
      SupportedCoreEventRelation handler statement w' := by
  -- SKETCH (L5): take `events := List.replicate w.steps .ordinary`.
  sorry

end SP1Clean.Execution
