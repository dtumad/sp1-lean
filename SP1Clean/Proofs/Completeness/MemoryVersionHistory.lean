import SP1Clean.Proofs.Completeness.MemoryHistory
import SP1Clean.Soundness.TouchChains

/-! # Time intervals of genuine Memory records

Adjacent Memory accesses at one location meet at the same timestamp and value. A probe
strictly before the next push observes the pulled value. At the exact push time and throughout
the final suffix it observes the new version. The empty history retains the incoming source.
-/

namespace SP1Clean.TraceGen.MemoryHistoryAccess

open Semantics

/-- Value after all chronological pushes at or before the specified time. -/
def heldAt (seed : BitVec 64) (time : ℕ) : List MemoryHistoryAccess → BitVec 64
  | [] => seed
  | access :: later =>
    if time < access.current then seed else heldAt access.pushed time later

/-- Enumerate values from real half-open access intervals, plus the final live version.
An empty location contributes its source value starting at genesis. -/
def matchingValues (since : ℕ) (seed : BitVec 64) (time : ℕ) : List MemoryHistoryAccess → List (BitVec 64)
  | [] => if since ≤ time then [seed] else []
  | a :: later =>
    (if a.previous ≤ time ∧ time < a.current then [a.pulled] else []) ++
      matchingValues a.current a.pushed time later

/-- Matching the intervals on a genuine linked and strictly advancing history yields exactly
one value after its first timestamp, even when consecutive accesses read back the same word. -/
theorem matchingValues_eq {since time : ℕ} {seed : BitVec 64} {records : List MemoryHistoryAccess}
    (first : ∀ a ∈ records.head?, a.previous = since ∧ a.pulled = seed)
    (linked : List.IsChain Continues records) (strict : ∀ a ∈ records, a.previous < a.current) :
    matchingValues since seed time records = if since ≤ time then [heldAt seed time records] else [] := by
  induction records generalizing since seed with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨rfl, rfl⟩ := first a (by simp)
    have advance := strict a List.mem_cons_self
    have links := List.isChain_cons.mp linked
    have tail := ih (fun b member => (links.1 b member).2) links.2
      (fun b member => strict b (List.mem_cons_of_mem _ member))
    by_cases before : time < a.previous
    · simp [matchingValues, tail, Nat.not_le_of_lt before, Nat.not_le_of_lt (before.trans advance)]
    · have entered := Nat.le_of_not_gt before
      by_cases after : a.current ≤ time
      · simp [matchingValues, heldAt, tail, after, entered, Nat.not_lt_of_ge after]
      · simp [matchingValues, heldAt, tail, after, entered, Nat.lt_of_not_ge after]

/-- An interior probe takes its value directly from the actual next pull. -/
theorem pulled_mem_matchingValues {a : MemoryHistoryAccess} {records : List MemoryHistoryAccess}
    {time : ℕ} (member : a ∈ records) (covers : a.previous ≤ time ∧ time < a.current)
    (since : ℕ) (seed : BitVec 64) : a.pulled ∈ matchingValues since seed time records := by
  induction records generalizing since seed with
  | nil => contradiction
  | cons b rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [matchingValues, covers]
    · exact List.mem_append_right _ (ih member b.current b.pushed)

private theorem terminal (a : MemoryHistoryAccess) (rest : List MemoryHistoryAccess)
    (links : List.IsChain Continues (a :: rest)) (strict : ∀ r ∈ a :: rest, r.previous < r.current) :
    let last := (a :: rest).getLast (by simp)
    a.current ≤ last.current ∧ ∀ seed time, last.current ≤ time → heldAt seed time (a :: rest) = last.pushed := by
  induction rest generalizing a with
  | nil =>
    refine ⟨le_rfl, fun seed time after => ?_⟩
    change a.current ≤ time at after
    simp [heldAt, Nat.not_lt_of_ge after]
  | cons b rest ih =>
    obtain ⟨h, chain⟩ := List.isChain_cons_cons.mp links
    obtain ⟨late, value⟩ := ih b chain (fun r mem => strict r (List.mem_cons_of_mem _ mem))
    have grows : a.current < b.current := h.2.1 ▸ strict b (by simp)
    have lower := grows.le.trans late
    refine ⟨lower, fun seed time after => ?_⟩
    rw [heldAt, ite_eq_right (Nat.not_lt_of_ge (lower.trans after))]
    exact value _ _ after

/-- The timestamp and value of a typed physical touch come directly from its pull and push
messages. The row's read-slot annotation is separate from both Memory-record timestamps. -/
def ofTouch {p : ℕ} [NeZero p] (touch : Soundness.TimedGrounding.Touch p) : MemoryHistoryAccess where
  loc := MemoryMsg.locOf touch.1.1
  previous := MemoryMsg.timeNat touch.1.1
  current := MemoryMsg.timeNat touch.2
  pulled := touch.1.1.value.toBitVec64
  pushed := touch.2.value.toBitVec64

/-- Physical per-location balance forces the head record and every intervening link,
including aliases within one row; the live predecessor therefore determines every probe
at its record time or later in this piece of the history. -/
theorem matchingValues_of_balance {p : ℕ} [NeZero p] {loc : MemLoc} {rowTime : ℕ}
    {live : Option (Channels.MemoryMsg (ZMod p))} {touches : List (Soundness.TimedGrounding.Touch p)}
    (nonempty : touches ≠ []) (ordered : Soundness.TimedGrounding.ChainOK loc rowTime touches)
    {later remaining : Multiset (Channels.MemoryMsg (ZMod p))}
    (gap : ∀ m ∈ later, rowTime + 8 ≤ MemoryMsg.timeNat m)
    (balance : Soundness.TimedGrounding.optMS live +
      ((↑(Soundness.TimedGrounding.chainPushes touches) : Multiset _) + later) =
      (↑(Soundness.TimedGrounding.chainPulls touches) : Multiset _) + remaining) :
    ∃ initial, live = some initial ∧ ∀ time ≥ MemoryMsg.timeNat initial,
      matchingValues (MemoryMsg.timeNat initial) initial.value.toBitVec64 time (touches.map ofTouch) =
        [heldAt initial.value.toBitVec64 time (touches.map ofTouch)] := by
  obtain ⟨head, linked, _, _⟩ := Soundness.TimedGrounding.chainForcing_step_of_gap nonempty ordered gap balance
  refine ⟨_, head, fun time after => ?_⟩
  rw [matchingValues_eq, ite_eq_left after]
  · cases touches with
    | nil => contradiction
    | cons a rest => simp [ofTouch]
  · apply (List.isChain_map ofTouch).mpr
    apply List.IsChain.imp_of_mem_imp _ linked
    intro a b ma mb same
    exact ⟨(ordered.pull_loc b mb).trans (ordered.pull_loc a ma).symm,
      congrArg MemoryMsg.timeNat same, congrArg (fun m : Channels.MemoryMsg (ZMod p) => m.value.toBitVec64) same⟩
  · intro a member
    obtain ⟨touch, inside, rfl⟩ := List.mem_map.mp member
    exact ordered.slot touch inside

end SP1Clean.TraceGen.MemoryHistoryAccess

namespace SP1Clean.TraceGen.MemoryLocationHistory

/-- Every timestamp of a nonempty canonical per-location history selects one held value,
from its incoming public record through the final version's unbounded suffix. -/
theorem matchingValues (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) (time : ℕ) :
    MemoryHistoryAccess.matchingValues 0 history.first.pulled time history.accesses =
      [MemoryHistoryAccess.heldAt history.first.pulled time history.accesses] := by
  rw [MemoryHistoryAccess.matchingValues_eq _ chain.adjacent strict, ite_eq_left (Nat.zero_le _)]
  intro a member
  have same : a = history.first := by
    rw [List.head?_eq_some_head history.nonempty] at member
    exact (Option.mem_some_iff.mp member).symm
  subst a
  exact ⟨chain.genesis, rfl⟩

/-- Between the actual predecessor and successor timestamp, the query reproduces the
successor's genuine pulled word. The lower endpoint is inclusive. -/
theorem heldAt_interval (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) {a : MemoryHistoryAccess}
    (member : a ∈ history.accesses) {time : ℕ} (covers : a.previous ≤ time ∧ time < a.current) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = a.pulled := by
  have seen := MemoryHistoryAccess.pulled_mem_matchingValues member covers 0 history.first.pulled
  rw [history.matchingValues chain strict time] at seen
  exact (List.mem_singleton.mp seen).symm

/-- At and after the last actual push the final version remains live indefinitely. -/
theorem heldAt_final (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current) {time : ℕ} (after : history.last.current ≤ time) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses = history.last.pushed := by
  cases eq : history.accesses with
  | nil => exact False.elim (history.nonempty eq)
  | cons a rest =>
    have linked := chain.adjacent
    rw [eq] at linked strict
    have final : history.last = (a :: rest).getLast (by simp) := by simp [last, eq]
    rw [final] at after ⊢
    exact (MemoryHistoryAccess.terminal a rest linked strict).2 _ _ after

end SP1Clean.TraceGen.MemoryLocationHistory
