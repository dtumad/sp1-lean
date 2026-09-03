import SP1Clean.Soundness.SyscallGrounding

/-! # The trail, once a syscall row can sit in the middle of it

The State-bus trail is extracted from endpoint balance and ordered by clock: `TrailRow` is
`DecodedInstructionRow ⊕ Array` today — an instruction row, or the halt table's raw row — and
`RankedGrounding` needs only that each edge strictly increases the clock.

Adding a syscall summand is mechanical. What is **not** mechanical is that the trail stops having a
shape.

**Today the trail is one of two things.** Either every row is `Sum.inl`, and `listAllInl` projects
`List (TrailRow p)` back to `List (DecodedInstructionRow p)` so the engine can walk instruction rows
only; or there is exactly one `Sum.inr`, and the halt branch splits the trail as
"prefix ++ that one ++ nil" — the `nil` justified by the fact that nothing can follow a halt edge,
since an instruction there would fetch at `pc = 1` and `fetchWord haltPc = none`.

**With `k` mid-shard syscall rows neither holds.** The trail is an arbitrary interleaving, and both
the projection and the split die with it. The engine has to consume `List (TrailRow p)` directly,
carrying a per-row duration, which is exactly what `walkG` was parameterized for.

**One further thing the halt case got for free and a mid-shard row does not.** The goodness filter
bounds the halt push's pc limbs on the *pulled* side only, because the halt push's pc is literally
`(1, 0, 0)` and is handled by hand. A mid-shard syscall row pushes a real 48-bit `pc + 4`, so it
needs genuine limb bounds on both sides or `canonState` stops preserving `pcBits`. -/

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A row of the State trail. The third constructor is the change: a syscall row is neither a decoded
instruction nor the terminal halt row, and — unlike the halt row — it is *walked* rather than cut out
before the walk begins. -/
inductive SyscallTrailRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 24 < p)]
  /-- A decoded instruction row: eight ticks, grounded by its chip's `advance`. -/
  | instruction (row : DecodedInstructionRow p)
  /-- A `StateBump` canonicalization row, whose edge is a self-loop and cancels before the trail. -/
  | bump (row : Array (ZMod p))
  /-- A syscall row: 264 ticks, grounded by the handler rather than by `try_step`. -/
  | syscall (r : SyscallInstrsChip.Inputs (ZMod p))

/-- The clock window each trail row occupies. This is the function that replaces the constant `8`
throughout the engine's clock accounting, and it is the same number `durationAt` reports for the
row's event — which is what makes the walk's positions and the timeline's starts one arithmetic. -/
def SyscallTrailRow.duration : SyscallTrailRow p → ℕ
  | .instruction _ => 8
  | .bump _ => 0
  | .syscall _ => 264

theorem SyscallTrailRow.eight_dvd_duration (row : SyscallTrailRow p) : 8 ∣ row.duration := by
  cases row
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨33, rfl⟩

/-- The State edge a trail row carries. -/
noncomputable def SyscallTrailRow.canonEdge (data : ProverData (ZMod p)) :
    SyscallTrailRow p → StateMsg (ZMod p) × StateMsg (ZMod p)
  | .instruction row => decodedStateEdge data row
  | .bump _ => default   -- SKETCH (L4): the StateBump self-loop, cancelled by the goodness filter
  | .syscall r =>
      (SyscallInstrsChip.statePulledMessage r, SyscallInstrsChip.statePushedMessage r)

/-- `RankedGrounding`'s obligation: every edge strictly advances the clock. Only strictness is
needed — the exact `264` is used later, by the clock accounting, not here. -/
theorem SyscallTrailRow.time_increases (data : ProverData (ZMod p)) (row : SyscallTrailRow p) :
    StateMsg.timeNat (row.canonEdge data).1 < StateMsg.timeNat (row.canonEdge data).2 := by
  -- SKETCH (L4): instruction rows by the existing `+8` step lemma; syscall rows by `+264`; bump
  -- rows never reach here, having cancelled before the trail is extracted.
  sorry

/-- **The goodness obligation a mid-shard syscall row owes.** The halt row is excused from bounding
its pushed pc because that pc is the literal `(1, 0, 0)`. A syscall row's push is a real `pc + 4`, so
both endpoints need limb bounds or `canonState` fails to preserve `pcBits`. -/
theorem syscallEdge_pcBounds (r : SyscallInstrsChip.Inputs (ZMod p))
    (spec : SyscallInstrsChip.Spec r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) (carry : (r.state.pc[0]).val + 4 < 2 ^ 16) :
    (∀ i : Fin 3, (r.state.pc[i]).val < 2 ^ 16) ∧
      (∀ i : Fin 3, (r.next_pc[i]).val < 2 ^ 16) := by
  -- SKETCH (L4): the pulled side is `PulledFacts`; the pushed side is `PcArm.Spec` plus the carry
  -- fact, which is what `StateBumpChip` supplies, exactly as upstream intends.
  sorry

/-! ## The shape the engine must now consume

The three statements below are what replace `listAllInl` and the halt-branch split. They are stated
over an arbitrary interleaving, which is the point. -/

/-- The transcript an ordered trail denotes, in trail order. -/
noncomputable def transcriptOfTrail (rows : List (SyscallTrailRow p)) : List ExecutionEvent :=
  rows.map fun row =>
    match row with
    | .instruction _ => .ordinary
    | .bump _ => .ordinary
    | .syscall r => .syscall (syscallEventOfRow r)

/-- Each trail row's own window is the duration its event reports at the same index. This is the
identity that lets the walk's positions be read off the timeline and vice versa. -/
theorem durationAt_transcriptOfTrail (rows : List (SyscallTrailRow p)) (k : ℕ)
    (hk : k < rows.length) :
    Semantics.durationAt (transcriptOfTrail rows) k = (rows[k]'hk).duration := by
  -- SKETCH (L4): `durationAt` reads `events[k]?`, which is the mapped row; the two `match`es agree
  -- arm for arm.
  sorry

/-- **The walk feed, with no shape assumption on the interleaving.** Given an ordered trail, its per
row facts, and the two balances, every row is grounded at the transcript's own timeline. This is what
`supported_core_witness_grounding` calls instead of projecting to instruction rows. -/
theorem trailWalk_grounded (handler : ExecutableSyscallHandler) (prog : GuestProgram)
    (initial : SailState) (initialClock : ℕ) (rows : List (SyscallTrailRow p)) :
    True := by
  -- SKETCH (L4): assemble `walkE` at `transcriptOfTrail rows`, taking each row's `RowFacts` from
  -- its own layer — `ordinaryRowFacts` for an instruction row, `syscallRowFacts` for a syscall row —
  -- and its timeline agreement from `durationAt_transcriptOfTrail` plus
  -- `timelineAgreement_of_durations`. Stated as `True` until the ordered-trail carrier is fixed.
  trivial

end SP1Clean.Soundness
