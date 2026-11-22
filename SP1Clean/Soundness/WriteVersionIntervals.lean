import SP1Clean.Soundness.WriteObservationHistory

/-! # WRITE probes between consecutive physical effect-slot pushes

Cut zero precedes the first event. A push in physical row `i` changes the value at cut
`i + 1`. Consequently the source interval begins at zero and the final interval includes
the cut after the last event. Both endpoints carry the original typed Memory messages
where present. Repeated probes can select the same interval without consuming it.
-/

namespace SP1Clean.Soundness.WriteObservationHistory

open Semantics Target
open Channels (MemoryMsg)

variable {p : ℕ}

/-- A half-open range of execution cuts between consecutive genuine pushes at one location.
A missing predecessor denotes genesis. A missing successor denotes the end of the segment. -/
structure VersionInterval (p : ℕ) where
  lower : ℕ
  upper : ℕ
  previous : Option (MemoryMsg (ZMod p))
  next : Option (MemoryMsg (ZMod p))

/-- The unchanged value throughout the interval, seeded from the incoming complete snapshot. -/
def VersionInterval.value (interval : VersionInterval p) (seed : Word (ZMod p)) : Word (ZMod p) :=
  (interval.previous.map (·.value)).getD seed

/-- Test whether an execution cut belongs to this version. -/
def VersionInterval.covers (interval : VersionInterval p) (cut : ℕ) : Bool :=
  decide (interval.lower ≤ cut ∧ cut < interval.upper)

/-- Test an incoming CPU clock directly against the original Memory message timestamps.
A missing boundary imposes no comparison on that side. -/
def VersionInterval.coversClock (interval : VersionInterval p) (clock : ℕ) : Bool :=
  interval.previous.all (fun msg => decide (MemoryMsg.timeNat msg < clock)) &&
    interval.next.all (fun msg => decide (clock < MemoryMsg.timeNat msg))

private def intervalsFrom (loc : MemLoc) (lower pos : ℕ) (previous : Option (MemoryMsg (ZMod p))) :
    List (RowFacts p) → List (VersionInterval p)
  | [] => [⟨lower, pos + 1, previous, none⟩]
  | row :: rest =>
    match effectPush? loc row with
    | none => intervalsFrom loc lower (pos + 1) previous rest
    | some msg => ⟨lower, pos + 1, previous, some msg⟩ :: intervalsFrom loc (pos + 1) (pos + 1) (some msg) rest

/-- Partition the cuts of the original physical rows without any extra guest Memory accesses. -/
def versionIntervals (rows : List (RowFacts p)) (loc : MemLoc) : List (VersionInterval p) :=
  intervalsFrom loc 0 0 none rows

private theorem endpoints_eq (loc : MemLoc) (rows : List (RowFacts p)) (lower pos : ℕ)
    (previous : Option (MemoryMsg (ZMod p))) :
    (intervalsFrom loc lower pos previous rows).filterMap (·.next) = rows.filterMap (effectPush? loc) ∧
    (intervalsFrom loc lower pos previous rows).filterMap (·.previous) =
      previous.toList ++ rows.filterMap (effectPush? loc) := by
  induction rows generalizing lower pos previous with
  | nil => cases previous <;> constructor <;> rfl
  | cons row rest ih =>
    cases found : effectPush? loc row with
    | none => simpa [intervalsFrom, found] using ih lower (pos + 1) previous
    | some msg =>
      obtain ⟨nextEq, prevEq⟩ := ih (pos + 1) (pos + 1) (some msg)
      cases previous <;> simp [intervalsFrom, found, nextEq, prevEq]

/-- Every selected role-stamped push occurs once as the end of its prior interval and
once as the start of its next interval, in physical order and preserving repetitions. -/
theorem versionIntervals_effects (rows : List (RowFacts p)) (loc : MemLoc) :
    (versionIntervals rows loc).filterMap (·.next) = rows.filterMap (effectPush? loc) ∧
    (versionIntervals rows loc).filterMap (·.previous) = rows.filterMap (effectPush? loc) := by
  simpa [versionIntervals] using endpoints_eq loc rows 0 0 none

/-- A non-genesis interval endpoint is the cut immediately following this actual typed
effect-slot push at the stated location. -/
def PushBoundary (rows : List (RowFacts p)) (loc : MemLoc) (cut : ℕ)
    (record : Option (MemoryMsg (ZMod p))) : Prop :=
  ∃ i row msg, rows[i]? = some row ∧ effectPush? loc row = some msg ∧ cut = i + 1 ∧ record = some msg

private theorem boundaries {full rows : List (RowFacts p)} {loc : MemLoc} {lower pos : ℕ}
    {previous : Option (MemoryMsg (ZMod p))} (last : pos + rows.length = full.length)
    (atRow : ∀ i row, rows[i]? = some row → full[pos + i]? = some row)
    (start : (lower = 0 ∧ previous = none) ∨ PushBoundary full loc lower previous)
    {v : VersionInterval p} (member : v ∈ intervalsFrom loc lower pos previous rows) :
    ((v.lower = 0 ∧ v.previous = none) ∨ PushBoundary full loc v.lower v.previous) ∧
    ((v.upper = full.length + 1 ∧ v.next = none) ∨ PushBoundary full loc v.upper v.next) := by
  induction rows generalizing lower pos previous with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    exact ⟨start, Or.inl ⟨by simpa using last, rfl⟩⟩
  | cons row rest ih =>
    have last' : pos + 1 + rest.length = full.length := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last
    have suffix i r (seen : rest[i]? = some r) : full[pos + 1 + i]? = some r := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atRow (i + 1) r seen
    cases found : effectPush? loc row with
    | none =>
      rw [intervalsFrom, found] at member
      exact ih last' suffix start member
    | some msg =>
      have boundary : PushBoundary full loc (pos + 1) (some msg) :=
        ⟨pos, row, msg, by simpa using atRow 0 row rfl, found, rfl, rfl⟩
      rw [intervalsFrom, found, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨start, Or.inr boundary⟩
      · exact ih last' suffix (Or.inr boundary) member

/-- Both ends of every version are authenticated physical pushes, or the appropriate
boundary of the segment. A proposed intermediate endpoint has no source in this inventory. -/
theorem versionIntervals_boundaries {rows : List (RowFacts p)} {loc : MemLoc} {v : VersionInterval p}
    (member : v ∈ versionIntervals rows loc) :
    ((v.lower = 0 ∧ v.previous = none) ∨ PushBoundary rows loc v.lower v.previous) ∧
    ((v.upper = rows.length + 1 ∧ v.next = none) ∨ PushBoundary rows loc v.upper v.next) :=
  boundaries (pos := 0) (by simp) (fun i r h => by simpa using h) (Or.inl ⟨rfl, rfl⟩) member

private theorem between_cuts (tl : Timeline) (i cut stamp : ℕ)
    (lo : tl.start i < stamp) (hi : stamp < tl.start (i + 1)) :
    decide (stamp < tl.start cut) = decide (i + 1 ≤ cut) ∧
    decide (tl.start cut < stamp) = decide (cut < i + 1) := by
  by_cases before : cut ≤ i
  · have prior := (tl.start_le_of_le before).trans_lt lo
    simp [prior, Nat.not_lt_of_ge prior.le, Nat.lt_succ_of_le before, Nat.not_le_of_lt (Nat.lt_succ_of_le before)]
  · have later := Nat.lt_of_not_ge before
    have after := hi.trans_le (tl.start_le_of_le later)
    simp [after, Nat.not_lt_of_ge after.le, Nat.succ_le_of_lt later, Nat.not_lt_of_ge (Nat.succ_le_of_lt later)]

private theorem time_of_offset (tl : Timeline) (i cut time rowTime offset : ℕ)
    (atRow : rowTime = tl.start i) (stamp : time = rowTime + offset) (positive : 0 < offset) (bounded : offset ≤ 4) :
    decide (time < tl.start cut) = decide (i + 1 ≤ cut) ∧ decide (tl.start cut < time) = decide (cut < i + 1) := by
  subst time rowTime
  apply between_cuts
  · exact Nat.lt_add_of_pos_right positive
  · have gap := tl.gap i
    omega

private theorem push_clock (tl : Timeline) (i cut : ℕ) (row : RowFacts p) (loc : MemLoc) (msg : MemoryMsg (ZMod p))
    (start : StateMsg.timeNat row.statePull = tl.start i) (found : effectPush? loc row = some msg) :
    decide (MemoryMsg.timeNat msg < tl.start cut) = decide (i + 1 ≤ cut) ∧
    decide (tl.start cut < MemoryMsg.timeNat msg) = decide (cut < i + 1) :=
  time_of_offset tl i cut (MemoryMsg.timeNat msg) (StateMsg.timeNat row.statePull) (TimedGrounding.writeOffset loc)
    start (effectPush?_some found).2.2 (by cases loc <;> simp) (TimedGrounding.writeOffset_le loc)

private theorem optional_clock {α : Type} (clockOf : α → ℕ) (clock cut i edge : ℕ)
    (record : Option α) (msg : α) (atEdge : edge = i + 1) (identified : record = some msg)
    (order : decide (clockOf msg < clock) = decide (i + 1 ≤ cut) ∧ decide (clock < clockOf msg) = decide (cut < i + 1)) :
    record.all (fun m => decide (clockOf m < clock)) = decide (edge ≤ cut) ∧
      record.all (fun m => decide (clock < clockOf m)) = decide (cut < edge) := by
  subst edge record
  exact order

private theorem boundary_clock {rows : List (RowFacts p)} {tl : Timeline}
    (times : ∀ i row, rows[i]? = some row → StateMsg.timeNat row.statePull = tl.start i)
    {loc : MemLoc} {edge : ℕ} {message : Option (MemoryMsg (ZMod p))}
    (boundary : PushBoundary rows loc edge message) (cut : ℕ) :
    (message.all (fun msg => decide (MemoryMsg.timeNat msg < tl.start cut)) = decide (edge ≤ cut)) ∧
    (message.all (fun msg => decide (tl.start cut < MemoryMsg.timeNat msg)) = decide (cut < edge)) := by
  obtain ⟨i, row, msg, present, found, edgeEq, msgEq⟩ := boundary
  exact optional_clock MemoryMsg.timeNat (tl.start cut) cut i edge message msg edgeEq msgEq
    (push_clock tl i cut row loc msg (times i row present) found)

/-- At actual incoming CPU clocks the endpoint comparisons select exactly the cut-indexed
version. Register and RAM effects both occur strictly inside their original row window. -/
theorem versionIntervals_clock {rows : List (RowFacts p)} {tl : Timeline}
    (times : ∀ i row, rows[i]? = some row → StateMsg.timeNat row.statePull = tl.start i)
    (loc : MemLoc) {cut : ℕ} (within : cut ≤ rows.length) :
    (versionIntervals rows loc).filter (·.coversClock (tl.start cut)) =
      (versionIntervals rows loc).filter (·.covers cut) := by
  apply List.filter_congr
  intro v member
  obtain ⟨left, right⟩ := versionIntervals_boundaries member
  have lo : v.previous.all (fun msg => decide (MemoryMsg.timeNat msg < tl.start cut)) = decide (v.lower ≤ cut) := by
    rcases left with ⟨start, empty⟩ | boundary
    · simp [start, empty]
    · exact (boundary_clock times boundary cut).1
  have hi : v.next.all (fun msg => decide (tl.start cut < MemoryMsg.timeNat msg)) = decide (cut < v.upper) := by
    rcases right with ⟨finish, empty⟩ | boundary
    · simp [finish, empty, Nat.lt_succ_of_le within]
    · exact (boundary_clock times boundary cut).2
  simp [VersionInterval.coversClock, VersionInterval.covers, lo, hi]

private theorem unchanged {loc : MemLoc} {rows : List (RowFacts p)}
    (untouched : ∀ row ∈ rows, effectPush? loc row = none)
    (lower pos : ℕ) (previous : Option (MemoryMsg (ZMod p))) :
    intervalsFrom loc lower pos previous rows = [⟨lower, pos + rows.length + 1, previous, none⟩] := by
  induction rows generalizing pos with
  | nil => rfl
  | cons row rest ih =>
    rw [intervalsFrom, untouched row List.mem_cons_self, ih (fun r h => untouched r (by simp [h]))]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A location with no effect-slot push has a single source version at every cut, even
if other genuine accesses repeatedly read back that location. -/
theorem versionIntervals_untouched {loc : MemLoc} {rows : List (RowFacts p)}
    (untouched : ∀ row ∈ rows, effectPush? loc row = none) :
    versionIntervals rows loc = [⟨0, rows.length + 1, none, none⟩] := by
  simpa [versionIntervals] using unchanged untouched 0 0 none

private theorem lower_bound {loc : MemLoc} {rows : List (RowFacts p)} {lower pos : ℕ}
    {previous : Option (MemoryMsg (ZMod p))} (ordered : lower ≤ pos)
    {v : VersionInterval p} (member : v ∈ intervalsFrom loc lower pos previous rows) : lower ≤ v.lower := by
  induction rows generalizing lower pos previous with
  | nil => simpa [intervalsFrom] using congrArg VersionInterval.lower (List.mem_singleton.mp member) |>.ge
  | cons row rest ih =>
    cases found : effectPush? loc row with
    | none =>
      rw [intervalsFrom, found] at member
      exact ih (by omega) member
    | some msg =>
      rw [intervalsFrom, found, List.mem_cons] at member
      rcases member with rfl | member
      · exact le_rfl
      · exact (show lower ≤ pos + 1 by omega).trans (ih le_rfl member)

private theorem selected {loc : MemLoc} {rows : List (RowFacts p)} {lower pos cut : ℕ}
    {previous : Option (MemoryMsg (ZMod p))} (seed : Word (ZMod p)) (ordered : lower ≤ pos)
    (afterLower : lower ≤ cut) (within : cut ≤ pos + rows.length) :
    ∃ v, (intervalsFrom loc lower pos previous rows).filter (·.covers cut) = [v] ∧
      v.value seed = (rows.take (cut - pos)).foldl (carry loc) ((previous.map (·.value)).getD seed) := by
  induction rows generalizing lower pos previous with
  | nil =>
    exact ⟨⟨lower, pos + 1, previous, none⟩, by simp [intervalsFrom, VersionInterval.covers, afterLower, show cut < pos + 1 by simpa using Nat.lt_succ_of_le within], by simp [VersionInterval.value]⟩
  | cons row rest ih =>
    have inside : cut ≤ (pos + 1) + rest.length := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using within
    cases found : effectPush? loc row with
    | none =>
      obtain ⟨v, only, value⟩ := ih (previous := previous) (by omega) afterLower inside
      refine ⟨v, by simpa only [intervalsFrom, found] using only, ?_⟩
      by_cases before : cut ≤ pos
      · simpa [Nat.sub_eq_zero_of_le before, Nat.sub_eq_zero_of_le (show cut ≤ pos + 1 by omega)] using value
      · have diff : cut - pos = (cut - (pos + 1)) + 1 := by omega
        simpa [diff, carry, found] using value
    | some msg =>
      rw [intervalsFrom, found]
      by_cases before : cut ≤ pos
      · have empty : (intervalsFrom loc (pos + 1) (pos + 1) (some msg) rest).filter (·.covers cut) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro v member possible
          have bound := lower_bound le_rfl member
          simp only [VersionInterval.covers, decide_eq_true_eq] at possible
          omega
        refine ⟨⟨lower, pos + 1, previous, some msg⟩, ?_, by simp [VersionInterval.value, Nat.sub_eq_zero_of_le before]⟩
        rw [List.filter_cons_of_pos (by simp [VersionInterval.covers, afterLower, show cut < pos + 1 by omega]), empty]
      · obtain ⟨v, only, value⟩ := ih (previous := some msg) le_rfl (by omega) inside
        have diff : cut - pos = (cut - (pos + 1)) + 1 := by omega
        exact ⟨v, by simpa [List.filter_cons, VersionInterval.covers, show ¬ cut < pos + 1 by omega] using only,
          by simpa [diff, carry, found] using value⟩

variable [Fact p.Prime]

/-- Every in-range cut selects exactly one physical version, whose four limbs agree with
the existing chronological prefix observer. This includes genesis, the final cut and
locations with no push anywhere in the segment. -/
theorem versionIntervals_at (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (loc : MemLoc)
    {cut : ℕ} (within : cut ≤ rows.length) :
    ∃ v, (versionIntervals rows loc).filter (·.covers cut) = [v] ∧
      v.value (bitVecToWord (snapshot.read loc)) = wordAt snapshot rows cut loc := by
  simpa [versionIntervals, wordAt] using
    (selected (loc := loc) (rows := rows) (pos := 0) (previous := none) (bitVecToWord (p := p) (snapshot.read loc))
      (Nat.le_refl 0) (Nat.zero_le cut) (by simpa using within))

/-- A word supplied to a read-only probe has a physical interval at the given cut. -/
def VersionedWord (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (cut : ℕ)
    (loc : MemLoc) (word : Word (ZMod p)) : Prop :=
  ∃ v ∈ versionIntervals rows loc, v.covers cut = true ∧ v.value (bitVecToWord (snapshot.read loc)) = word

/-- The private interval join and the existing physical prefix scan accept exactly the same
four-limb word. Each probe can independently reuse the same matching version. -/
theorem versionedWord_iff {snapshot : MemorySnapshot} {rows : List (RowFacts p)}
    {cut : ℕ} (within : cut ≤ rows.length) (loc : MemLoc) (word : Word (ZMod p)) :
    VersionedWord snapshot rows cut loc word ↔ word = wordAt snapshot rows cut loc := by
  obtain ⟨v, only, value⟩ := versionIntervals_at snapshot rows loc within
  have unique w : w ∈ (versionIntervals rows loc).filter (·.covers cut) ↔ w = v := by
    rw [only, List.mem_singleton]
  constructor
  · rintro ⟨w, member, covers, eq⟩
    obtain rfl := (unique w).mp (List.mem_filter.mpr ⟨member, covers⟩)
    exact eq.symm.trans value
  · rintro rfl
    obtain ⟨member, covers⟩ := List.mem_filter.mp ((unique v).mpr rfl)
    exact ⟨v, member, covers, value⟩

end SP1Clean.Soundness.WriteObservationHistory
