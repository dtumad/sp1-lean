import SP1Clean.Soundness.TimedGrounding
import SP1Clean.Model.Semantics.GenericTruth
import SP1Clean.Model.Semantics.EventTime

/-! # The grounding walk over an arbitrary trajectory

`TimedGrounding.walkT` is the engine: given per-row step and frame facts, the row-shape discipline,
the timeline agreement, a true head, a true genesis frontier, and the two multiset balances, every
pull's guarantee holds. Its statement is already timeline-relative — `RowOKCore`'s window is a
`+8 ≤` lower bound, not an exact width — so a 264-tick row satisfies its *shape* obligations
verbatim.

What it is not generic in is the **step relation**. `LocalStateTruthT` demands a `SailChain`, and a
syscall step deliberately is not one, so no timeline makes a syscall row a walk member.

This file states the walk once over `Semantics.Trajectory` and derives the two instantiations:

* `walkT` — at `sailTrajectory`, recovering the existing engine *unchanged*. This is the acceptance
  test for the whole refactor: if a consumer of `walkT` has to move, the generalization was
  mis-stated.
* `walkE` — at `Semantics.eventTrajectory`, where a step may be an ordinary Sail step or a handled
  syscall, and the timeline is the transcript's own prefix-summed durations.

The three predicate bridges that `GenericTruth.lean` could not state — its import does not reach
`FrameFactT`/`LiveOKT`/`GroundedT` — are here, beside the walk that consumes them. -/

namespace SP1Clean.Soundness.TimedGrounding

open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The remaining Sail bridges -/

omit [Fact (2 ^ 17 < p)] in
theorem frameFactG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {r : RowFacts p} :
    FrameFactG program (sailTrajectory initial) initial tl r ↔ FrameFactT program initial tl r := by
  unfold FrameFactG FrameFactT
  simp only [localStateTruthG_sail, localValueAtG_sail]

omit [Fact (2 ^ 17 < p)] in
theorem liveOKG_sail {initial : SailState} {tl : Timeline} {t : ℕ}
    {live : MemLoc → Option (MemoryMsg (ZMod p))} :
    LiveOKG (sailTrajectory initial) initial tl t live ↔ LiveOKT initial tl t live := by
  unfold LiveOKG LiveOKT
  simp only [localMemTruthG_sail, localValueAtG_sail]

omit [Fact (2 ^ 17 < p)] in
theorem groundedG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {r : RowFacts p} :
    GroundedG program (sailTrajectory initial) initial tl r ↔ GroundedT program initial tl r := by
  unfold GroundedG GroundedT
  simp only [localStateTruthG_sail, localMemTruthG_sail, localValueAtG_sail]

/-! ## The walk

The proof is `walkT`'s, with `chainState initial` replaced by the trajectory parameter throughout.
Nothing in the body inspects *how* a step was taken: the layer-A window arithmetic is
`RowOKCore`-only, layer B is the chain machinery over row-relative touch offsets, and layer C is
whatever `LocalStepFactG` supplies. The Sail-specific reasoning all lives in the *callers* that
discharge `LocalStepFactG`, which is exactly where a syscall row differs. -/

/-- **The grounding walk, over any trajectory.** Statement identical to `walkT`'s with the
`…T` predicates replaced by their `…G` forms and the trajectory made a parameter. -/
theorem walkG (program : GuestProgram) (traj : Trajectory) (initial : SailState) (tl : Timeline)
    (initialClock : ℕ) (fin : StateMsg (ZMod p))
    (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactG program traj initial tl r) →
      (∀ r ∈ rows, FrameFactG program traj initial tl r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ, StateMsg.timeNat r.statePull = tl.start n →
        StateMsg.timeNat r.statePush = tl.start (n + 1)) →
      LocalStateTruthG program traj tl head →
      LiveOKG traj initial tl (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedG program traj initial tl r) ∧
        LocalStateTruthG program traj tl fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthG traj initial tl m ∧
          LocalValueAtG traj initial tl loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin := by
  -- SKETCH (L1): port `walkT`'s induction, replacing `chainState initial` by `traj`. The body is
  -- already timeline-relative; the only edits are the microtime readers, which become the `…G`
  -- forms defined over the trajectory parameter.
  sorry

/-- **The Sail instantiation recovers `walkT` exactly.** This is the refactor's acceptance test: it
must hold with no change to `walkT`'s statement. -/
theorem walkT_of_walkG (program : GuestProgram) (initial : SailState) (tl : Timeline)
    (initialClock : ℕ) (fin : StateMsg (ZMod p))
    (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactT program initial tl r) →
      (∀ r ∈ rows, FrameFactT program initial tl r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ, StateMsg.timeNat r.statePull = tl.start n →
        StateMsg.timeNat r.statePush = tl.start (n + 1)) →
      LocalStateTruthT program initial tl head →
      LiveOKT initial tl (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedT program initial tl r) ∧
        LocalStateTruthT program initial tl fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthT initial tl m ∧
          LocalValueAtT initial tl loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin := by
  intro N rows head live hlen hstep hframe hrow htl hhead hlive hsbal hmbal
  have := walkG program (sailTrajectory initial) initial tl initialClock fin finM N rows head live
    hlen
    (fun r hr => localStepFactG_sail.mpr (hstep r hr))
    (fun r hr => frameFactG_sail.mpr (hframe r hr))
    hrow htl
    (localStateTruthG_sail.mpr hhead)
    (liveOKG_sail.mpr hlive)
    hsbal hmbal
  obtain ⟨hg, hfin, hfinM⟩ := this
  refine ⟨fun r hr => groundedG_sail.mp (hg r hr), localStateTruthG_sail.mp hfin, ?_⟩
  intro loc m hm
  obtain ⟨hkey, htruth, hval, htime⟩ := hfinM loc m hm
  exact ⟨hkey, localMemTruthG_sail.mp htruth, localValueAtG_sail.mp hval, htime⟩

/-- **The event instantiation.** A step may be an ordinary Sail step or a handled syscall, and the
timeline is the transcript's own prefix-summed durations — so a 264-tick row occupies exactly one
timeline step, by construction rather than by hypothesis. -/
theorem walkE (handler : Machine.ExecutableSyscallHandler) (program : GuestProgram)
    (events : List Machine.ExecutionEvent) (initial : SailState) (initialClock : ℕ)
    (fin : StateMsg (ZMod p)) (finM : MemLoc → Option (MemoryMsg (ZMod p))) :
    ∀ (N : ℕ) (rows : List (RowFacts p)) (head : StateMsg (ZMod p))
      (live : MemLoc → Option (MemoryMsg (ZMod p))),
      rows.length = N →
      (∀ r ∈ rows, LocalStepFactG program (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) r) →
      (∀ r ∈ rows, FrameFactG program (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) r) →
      (∀ r ∈ rows, RowOKCore initialClock r) →
      (∀ r ∈ rows, ∀ n : ℕ,
        StateMsg.timeNat r.statePull = (eventTimeline events initialClock).start n →
        StateMsg.timeNat r.statePush = (eventTimeline events initialClock).start (n + 1)) →
      LocalStateTruthG program (eventTrajectory handler program events initial)
        (eventTimeline events initialClock) head →
      LiveOKG (eventTrajectory handler program events initial) initial
        (eventTimeline events initialClock) (StateMsg.timeNat head) live →
      (head ::ₘ (↑(rows.map (·.statePush)) : Multiset (StateMsg (ZMod p)))
        = fin ::ₘ ↑(rows.map (·.statePull))) →
      (∀ loc : MemLoc, optMS (live loc) + pushesAt rows loc
        = optMS (finM loc) + pullsAt rows loc) →
      (∀ r ∈ rows, GroundedG program (eventTrajectory handler program events initial) initial
          (eventTimeline events initialClock) r) ∧
        LocalStateTruthG program (eventTrajectory handler program events initial)
          (eventTimeline events initialClock) fin ∧
        ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finM loc = some m →
          MemoryMsg.locOf m = loc ∧
          LocalMemTruthG (eventTrajectory handler program events initial) initial
            (eventTimeline events initialClock) m ∧
          LocalValueAtG (eventTrajectory handler program events initial) initial
            (eventTimeline events initialClock) loc (StateMsg.timeNat fin) m.value ∧
          MemoryMsg.timeNat m ≤ StateMsg.timeNat fin :=
  walkG program (eventTrajectory handler program events initial) initial
    (eventTimeline events initialClock) initialClock fin finM

end SP1Clean.Soundness.TimedGrounding
