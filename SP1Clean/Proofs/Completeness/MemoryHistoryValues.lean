import SP1Clean.Proofs.Completeness.MemoryVersionHistory

/-! # Applying the canonical Memory transfers to their architectural values

The existing instruction plan checks each incoming value before posting the new one. Expanding
the plan's genuine MemoryBump records preserves that exact final value image. The same physical
transfer clocks determine the word held at an intervening query.
-/

namespace SP1Clean.TraceGen.MemoryHistoryAccess

open Semantics

/-- Apply the posted values of the complete transfer stream in their original occurrence order. -/
def post (values : LocationValues) (records : List MemoryHistoryAccess) : LocationValues :=
  records.foldl (fun prior a => Function.update prior a.loc (some a.pushed)) values

/-- Splitting the transferred values at any occurrence recovers the same final image. -/
theorem post_append (initial : LocationValues) (first second : List MemoryHistoryAccess) :
    post initial (first ++ second) = post (post initial first) second := List.foldl_append

/-- A batch whose published words agree with the final image changes only the listed locations. -/
theorem post_eq_of_values {records : List MemoryHistoryAccess} {initial final : LocationValues}
    (written : ∀ a ∈ records, some a.pushed = final a.loc)
    (framed : ∀ loc, (∀ a ∈ records, a.loc ≠ loc) → initial loc = final loc) : post initial records = final := by
  induction records generalizing initial with
  | nil => exact funext fun loc => framed loc (by simp)
  | cons a records ih =>
    apply ih (initial := Function.update initial a.loc (some a.pushed))
    · exact fun b mem => written b (List.mem_cons_of_mem a mem)
    · intro loc fresh
      by_cases same : loc = a.loc
      · subst loc; rw [Function.update_self]; exact written a List.mem_cons_self
      · rw [Function.update_of_ne same]
        apply framed
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (Ne.symm same) (fresh)

private theorem post_single_touch (values : LocationValues) (frontier : AccessFrontier) (base : ℕ) (touch : PlannedTouch) :
    post values (ofScheduledAccess base (scheduleAccess frontier base touch)) =
      Function.update values touch.loc (some touch.pushed) := by
  cases emitted : memoryBumpEvent? frontier base touch with
  | none =>
    rw [ofScheduledAccess_noBump (by exact emitted)]
    rfl
  | some event =>
    rw [ofScheduledAccess_someBump (by exact emitted)]
    obtain ⟨index, located, _, rfl⟩ := memoryBumpEvent?_shape emitted
    change Function.update (Function.update values (.reg (BitVec.ofNat 5 index.toNat)) _) touch.loc _ = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← located, Function.update_idem]
    rfl

/-- Every successful canonical plan produces the same location values when expanded into its
actual instruction and refresh transfers, including aliases within one row. -/
theorem post_of_schedule {plan : InstructionAccessPlan} {source target : LocationValues}
    (valid : plan.RunsFrom source target) (frontier : AccessFrontier) (base : ℕ) :
    post source (ofAccessSchedule base (scheduleAccessPlan frontier base plan)) = target := by
  induction plan generalizing source frontier with
  | nil => exact (InstructionAccessPlan.runsFrom_nil_iff.mp valid).symm
  | cons touch later ih =>
    have run := (InstructionAccessPlan.runsFrom_cons_iff.mp valid).2
    rw [scheduleAccessPlan_cons, ofAccessSchedule_cons, post_append, post_single_touch]
    exact ih run _

/-- Every expanded transfer starts after the CPU clock and finishes within the four physical
access offsets. A refresh at the start of a high window uses the first of those offsets. -/
theorem current_in_window (frontier : AccessFrontier) (base : ℕ) (plan : InstructionAccessPlan)
    {access : MemoryHistoryAccess} (present : access ∈ ofAccessSchedule base (scheduleAccessPlan frontier base plan)) :
    base < access.current ∧ access.current ≤ base + 4 := by
  obtain ⟨scheduled, occurs, member⟩ := List.mem_flatMap.mp present
  rcases List.mem_append.mp member with bump | instruction
  · obtain ⟨event, generated, rfl⟩ := List.mem_map.mp bump
    have actual : event ∈ (scheduleAccessPlan frontier base plan).memoryBumps :=
      List.mem_filterMap.mpr ⟨scheduled, occurs, Option.mem_toList.mp generated⟩
    change base < event.currTs ∧ event.currTs ≤ base + 4
    rw [scheduleAccessPlan_memoryBump_currTs actual]
    omega
  · cases List.mem_singleton.mp instruction
    have positive := scheduled.stamped.touch.slot.recordOffset_pos
    have small := scheduled.stamped.touch.slot.recordOffset_le_four
    change base < base + scheduled.stamped.touch.slot.recordOffset ∧ base + scheduled.stamped.touch.slot.recordOffset ≤ base + 4
    omega

/-- At a cut separating earlier and later pushes, the published held word is exactly the
architectural value after applying the earlier transfers, including the empty-location case. -/
theorem heldAt_post {before after : List MemoryHistoryAccess} {time : ℕ}
    (earlier : ∀ a ∈ before, a.current ≤ time) (later : ∀ a ∈ after, time < a.current)
    {values : LocationValues} (loc : MemLoc) (seed : BitVec 64) (initial : values loc = some seed) :
    some (heldAt seed time (memoryHistoryAt (before ++ after) loc)) = post values before loc := by
  induction before generalizing values seed with
  | nil =>
    simp only [List.nil_append, post, List.foldl_nil, initial, Option.some.injEq]
    cases h : memoryHistoryAt after loc with
    | nil => rfl
    | cons a tail =>
      have occurs : a ∈ memoryHistoryAt after loc := h ▸ List.mem_cons_self
      rw [heldAt, ite_eq_left (later a (List.mem_filter.mp occurs).1)]
  | cons a rest ih =>
    have step := earlier a List.mem_cons_self
    have tail := fun b (mem : b ∈ rest) => earlier b (List.mem_cons_of_mem a mem)
    simp only [List.cons_append, memoryHistoryAt, List.filter_cons] at ⊢
    by_cases same : a.loc = loc
    · simp only [same, decide_true, ↓reduceIte, heldAt, ite_eq_right (Nat.not_lt_of_ge step)]
      exact ih tail a.pushed (values := Function.update values a.loc (some a.pushed)) (by simp [same])
    · simp only [same, decide_false]
      exact ih tail seed (values := Function.update values a.loc (some a.pushed)) (by simpa [Function.update_of_ne (Ne.symm same)] using initial)

end SP1Clean.TraceGen.MemoryHistoryAccess
