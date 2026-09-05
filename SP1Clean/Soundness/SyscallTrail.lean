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

/-- Every trail row's window is positive — **except the bump row's**, which is a self-loop of width
zero. This is the fact that makes `time_increases` need its side condition. -/
theorem SyscallTrailRow.duration_pos (row : SyscallTrailRow p) (noBump : ∀ a, row ≠ .bump a) :
    0 < row.duration := by
  cases hrow : row with
  | instruction _ => norm_num [SyscallTrailRow.duration]
  | bump a => exact absurd hrow (noBump a)
  | syscall _ => norm_num [SyscallTrailRow.duration]

/-- `RankedGrounding`'s obligation: every edge strictly advances the clock — reduced to the two facts
it actually rests on, neither of which the sketch's hypothesis-free statement admitted.

**The bump arm makes the bare statement false.** `canonEdge` sends a bump row to `default`, whose two
endpoints are the *same* message, so the strict inequality fails outright rather than going unproved.
Bump rows cancel before the trail is extracted, and `noBump` is where that has to be said.

**The advance is a canonicalization premise, not arithmetic.** A syscall row's push is
`clk_low + 264` and an instruction row's is `clk_low + 8`, both computed by upstream without a range
constraint; on a wrapping row the pushed message's `timeNat` is not the sum at all. So "this edge
advances by this row's duration" is supplied by `StateBumpChip`, exactly as the pc's `+ 4` carry is,
and it is the *same* non-canonicality on the clock axis that `syscallEdge_pcBounds` handles on the pc
axis. -/
theorem SyscallTrailRow.time_increases (data : ProverData (ZMod p)) (row : SyscallTrailRow p)
    (noBump : ∀ a, row ≠ .bump a)
    (advances : StateMsg.timeNat (row.canonEdge data).2
      = StateMsg.timeNat (row.canonEdge data).1 + row.duration) :
    StateMsg.timeNat (row.canonEdge data).1 < StateMsg.timeNat (row.canonEdge data).2 := by
  have hpos := row.duration_pos noBump
  omega

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

/-- Each trail row's own window is the duration its event reports at the same index — **on a
bump-free trail**, and the side condition is not bookkeeping.

`SyscallTrailRow` has a zero-width arm and `ExecutionEvent` does not, so a `.bump` row is mapped to
`.ordinary` and its event claims eight ticks where the row claims none. Without the hypothesis this
statement is *false*, not merely unproved. That is the price of walking the pre-filter row type:
`WalkedRow` is the post-filter one, it has no zero-width arm, and
`SyscallGrounding.durationAt_transcriptOf` states the same identity there with no side condition at
all. The trail should be projected to `WalkedRow` once the goodness filter has cancelled the
self-loops, and this lemma is the reminder of where that projection has to happen. -/
theorem durationAt_transcriptOfTrail (rows : List (SyscallTrailRow p)) (k : ℕ)
    (hk : k < rows.length) (noBump : ∀ row ∈ rows, ∀ a, row ≠ .bump a) :
    Semantics.durationAt (transcriptOfTrail rows) k = (rows[k]'hk).duration := by
  have hlen : k < (transcriptOfTrail rows).length := by simpa [transcriptOfTrail] using hk
  rw [Semantics.durationAt, List.getElem?_eq_getElem hlen]
  simp only [transcriptOfTrail, List.getElem_map]
  have hmem : rows[k] ∈ rows := List.getElem_mem hk
  cases hrow : rows[k] with
  | instruction row => rfl
  | bump a => exact absurd hrow (noBump _ hmem a)
  | syscall r => rfl

/-- **The walk feed, with no shape assumption on the interleaving.** Given an ordered walk of mixed
rows, each row's own four obligations at its own index, and the two balances, every row is grounded
at the transcript's own timeline — and so are the shard's final State message and its Memory
frontier.

This is what `supported_core_witness_grounding` calls instead of projecting to instruction rows, and
it is the statement that replaces `listAllInl` and the halt-branch split. Nothing here assumes an
arm ordering: `rows` is an arbitrary interleaving, and the only thing tying a row to the transcript
is its index, through `positioned_of_walkOrder` and `walkedRow_timeStep`.

⚠ The carrier is `WalkedRow`, not `SyscallTrailRow`. The trail type has a zero-width `.bump` arm and
`ExecutionEvent` does not, so the transcript identity fails on it outright; bump rows are self-loops
that the goodness filter cancels before the trail is extracted, and the projection onto `WalkedRow`
is where that cancellation has to be spent. -/
theorem trailWalk_grounded (handler : ExecutableSyscallHandler) (prog : Target.GuestProgram)
    (data : ProverData (ZMod p)) (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (rows : List (WalkedRow p))
    (initial : SailState) (initialClock : ℕ)
    (fin : StateMsg (ZMod p)) (head : StateMsg (ZMod p))
    (finM live : Semantics.MemLoc → Option (Channels.MemoryMsg (ZMod p)))
    (stepAt : ∀ (k : ℕ) (hk : k < rows.length),
      Semantics.LocalStepFactG prog
        (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
        (Semantics.eventTimeline (transcriptOf data rows) initialClock)
        (WalkedRow.facts g (rows[k]'hk)))
    (frameAt : ∀ (k : ℕ) (hk : k < rows.length),
      Semantics.FrameFactG prog
        (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
        (Semantics.eventTimeline (transcriptOf data rows) initialClock)
        (WalkedRow.facts g (rows[k]'hk)))
    (rowOKAt : ∀ (k : ℕ) (hk : k < rows.length),
      TimedGrounding.RowOKCore initialClock (WalkedRow.facts g (rows[k]'hk)))
    (widthAt : ∀ (k : ℕ) (hk : k < rows.length),
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePush
        = StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
          + (rows[k]'hk).duration)
    (pullAt : ∀ (k : ℕ) (hk : k < rows.length),
      StateMsg.timeNat (WalkedRow.facts g (rows[k]'hk)).statePull
        = (Semantics.eventTimeline (transcriptOf data rows) initialClock).start k)
    (headTruth : Semantics.LocalStateTruthG prog
      (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial)
      (Semantics.eventTimeline (transcriptOf data rows) initialClock) head)
    (liveHead : Semantics.LiveOKG
      (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
      (Semantics.eventTimeline (transcriptOf data rows) initialClock)
      (StateMsg.timeNat head) live)
    (stateBalance : head ::ₘ
        (↑((rows.map (WalkedRow.facts g)).map (·.statePush)) :
          Multiset (StateMsg (ZMod p)))
      = fin ::ₘ ↑((rows.map (WalkedRow.facts g)).map (·.statePull)))
    (memoryBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (live loc)
          + TimedGrounding.pushesAt (rows.map (WalkedRow.facts g)) loc
        = TimedGrounding.optMS (finM loc)
          + TimedGrounding.pullsAt (rows.map (WalkedRow.facts g)) loc) :
    (∀ r ∈ rows.map (WalkedRow.facts g),
        Semantics.GroundedG prog
          (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
          (Semantics.eventTimeline (transcriptOf data rows) initialClock) r) ∧
      Semantics.LocalStateTruthG prog
        (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial)
        (Semantics.eventTimeline (transcriptOf data rows) initialClock) fin ∧
      ∀ (loc : Semantics.MemLoc) (m : Channels.MemoryMsg (ZMod p)), finM loc = some m →
        Semantics.MemoryMsg.locOf m = loc ∧
        Semantics.LocalMemTruthG
          (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
          (Semantics.eventTimeline (transcriptOf data rows) initialClock) m ∧
        Semantics.LocalValueAtG
          (Semantics.eventTrajectory handler prog (transcriptOf data rows) initial) initial
          (Semantics.eventTimeline (transcriptOf data rows) initialClock) loc
          (StateMsg.timeNat fin) m.value ∧
        Semantics.MemoryMsg.timeNat m ≤ StateMsg.timeNat fin := by
  have indexOf : ∀ r ∈ rows.map (WalkedRow.facts g),
      ∃ (k : ℕ) (hk : k < rows.length), r = WalkedRow.facts g (rows[k]'hk) := by
    intro r hr
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
    obtain ⟨k, hk, hrk⟩ := List.getElem_of_mem hrow
    exact ⟨k, hk, by rw [hrk]⟩
  exact TimedGrounding.walkE handler prog (transcriptOf data rows) initial initialClock fin finM
    (rows.map (WalkedRow.facts g)).length (rows.map (WalkedRow.facts g)) head live rfl
    (fun r hr => by obtain ⟨k, hk, rfl⟩ := indexOf r hr; exact stepAt k hk)
    (fun r hr => by obtain ⟨k, hk, rfl⟩ := indexOf r hr; exact frameAt k hk)
    (fun r hr => by obtain ⟨k, hk, rfl⟩ := indexOf r hr; exact rowOKAt k hk)
    (fun r hr => by
      obtain ⟨k, hk, rfl⟩ := indexOf r hr
      exact walkedRow_timeStep data g rows initialClock k hk (pullAt k hk) (widthAt k hk))
    headTruth liveHead stateBalance memoryBalance

end SP1Clean.Soundness
