import SP1Clean.Soundness.MemoryRecordChain

/-! # Transporting word range checks through physical Memory history

Before any row writes, earlier rows have well-formed outputs. Within its read window
an access from the same or a later row can only read a value back unchanged. The
induction therefore covers register aliases in one instruction and refreshes with
arbitrary timestamps, including a RAM update before its register operand readbacks.
-/

namespace SP1Clean.Soundness.MemoryRecordChain

open Channels Semantics TimedGrounding NativeCore

variable {p : ℕ}
private abbrev Msg (p : ℕ) := MemoryMsg (ZMod p)

private theorem read_before_write (loc : MemLoc) : readWindow loc < writeOffset loc := by cases loc <;> simp

private theorem earlier_records [Fact p.Prime] {first last : Msg p} {path : List (Pair p)} (walk : Walk.IsWalk id first last path)
    {bound : ℕ} (seed : MemoryMsg.timeNat first ≤ bound → MemoryMsg.isU64 first)
    (strict : ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2)
    (step : ∀ e ∈ path, MemoryMsg.timeNat e.2 ≤ bound → MemoryMsg.isU64 e.1 → MemoryMsg.isU64 e.2) :
    (∀ e ∈ path, MemoryMsg.timeNat e.1 ≤ bound → MemoryMsg.isU64 e.1) ∧
      (MemoryMsg.timeNat last ≤ bound → MemoryMsg.isU64 last) := by
  induction path generalizing first with
  | nil => exact ⟨fun _ hm => (List.not_mem_nil hm).elim, (show first = last from walk) ▸ seed⟩
  | cons head rest ih =>
    obtain ⟨rfl, tail⟩ := walk
    have next (early : MemoryMsg.timeNat head.2 ≤ bound) := step head (List.mem_cons_self ..) early
      (seed ((strict head (List.mem_cons_self ..)).le.trans early))
    have later := ih tail next (fun e member => strict e (List.mem_cons_of_mem _ member))
      (fun e member => step e (List.mem_cons_of_mem _ member))
    refine ⟨fun e member => ?_, later.2⟩
    rcases List.mem_cons.mp member with rfl | inside
    · exact seed
    · exact later.1 e inside

private theorem prior_in_read_window {time : ℕ} {t : Touch p} (valid : TouchOK time t.1 t.2)
    (strict : MemoryMsg.timeNat t.1.1 < MemoryMsg.timeNat t.2) :
    MemoryMsg.timeNat t.1.1 ≤ time + readWindow (MemoryMsg.locOf t.1.1) := by
  rcases valid.push_kind with back | write
  · exact strict.le.trans (back.2 ▸ valid.read_hi)
  · have offset : writeOffset (MemoryMsg.locOf t.2) = readWindow (MemoryMsg.locOf t.1.1) + 1 := by
      rw [valid.loc_eq]; cases MemoryMsg.locOf t.1.1 <;> rfl
    omega

private theorem in_inventory (cpu : List (RowFacts p)) (extra : List (Touch p)) (refresh : List (Pair p))
    {row : RowFacts p} (owner : row ∈ cpu) {t : Touch p} (inside : t ∈ rowTouches row) :
    (t.1.1, t.2) ∈ pairs cpu extra refresh :=
  List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_append_left _ (List.mem_flatMap.mpr ⟨row, owner, inside⟩), rfl⟩)

/-- Signed physical Memory histories and row-local range propagation force every consumed
word and final frontier word to have four 16-bit limbs. Only an original row's own
incoming words enter its local range implication. -/
theorem words_of_histories [Fact p.Prime] (cpu : List (RowFacts p)) (extra : List (Touch p)) (refresh : List (Pair p))
    (initial final : MemLoc → Option (Msg p))
    (histories : ∀ loc, History (atLocation loc (pairs cpu extra refresh)) (initial loc) (final loc))
    (seeds : ∀ loc m, initial loc = some m → MemoryMsg.isU64 m)
    (localTouches : ∀ row ∈ cpu, ∀ t ∈ rowTouches row, TouchOK (StateMsg.timeNat row.statePull) t.1 t.2)
    (localWords : ∀ row ∈ cpu, (∀ t ∈ rowTouches row, MemoryMsg.isU64 t.1.1) → ∀ t ∈ rowTouches row, MemoryMsg.isU64 t.2)
    (host : ∀ t ∈ extra, MemoryMsg.isU64 t.2)
    (bumps : ∀ e ∈ refresh, e.2.value = e.1.value) :
    (∀ e ∈ pairs cpu extra refresh, MemoryMsg.isU64 e.1) ∧ ∀ loc m, final loc = some m → MemoryMsg.isU64 m := by
  let edges := pairs cpu extra refresh
  have prefixAt (loc : MemLoc) (endTime : ℕ)
      (advance : ∀ e ∈ atLocation loc edges, MemoryMsg.timeNat e.2 ≤ endTime → MemoryMsg.isU64 e.1 → MemoryMsg.isU64 e.2) :
      (∀ e ∈ atLocation loc edges, MemoryMsg.timeNat e.1 ≤ endTime → MemoryMsg.isU64 e.1) ∧
        ∀ m, final loc = some m → MemoryMsg.timeNat m ≤ endTime → MemoryMsg.isU64 m := by
    rcases histories loc with ⟨_, done, empty⟩ | ⟨first, last, path, start, finish, perm, walk, _, strict⟩
    · exact ⟨fun _ inside => (List.not_mem_nil (empty ▸ inside)).elim,
        fun m member => (Option.some_ne_none m (member.symm.trans done)).elim⟩
    have segment :=  earlier_records walk (fun _ => seeds loc first start) strict (fun e inside => advance e (perm.mem_iff.mp inside))
    exact ⟨fun e inside => segment.1 e (perm.mem_iff.mpr inside), fun m member => Option.some.inj (finish.symm.trans member) ▸ segment.2⟩
  have rank {e : Pair p} (member : e ∈ edges) : MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2 := by
    let loc := MemoryMsg.locOf e.2
    have atLoc : e ∈ atLocation loc edges := List.mem_filter.mpr ⟨member, by simp [loc]⟩
    rcases histories loc with ⟨_, _, empty⟩ | ⟨_, _, _, _, _, perm, _, _, strict⟩
    · exact (List.not_mem_nil (empty ▸ atLoc)).elim
    · exact strict e (perm.mem_iff.mpr atLoc)
  let Closed (time : ℕ) := ∀ row ∈ cpu, StateMsg.timeNat row.statePull = time → ∀ t ∈ rowTouches row, MemoryMsg.isU64 t.2
  have before (time : ℕ) (ih : ∀ previous < time, Closed previous) (loc : MemLoc) :
      ∀ e ∈ atLocation loc edges, MemoryMsg.timeNat e.2 ≤ time + readWindow loc → MemoryMsg.isU64 e.1 → MemoryMsg.isU64 e.2 := by
    intro e selected byCut good
    obtain ⟨inside, same⟩ := List.mem_filter.mp selected
    have location : MemoryMsg.locOf e.2 = loc := of_decide_eq_true same
    rcases List.mem_append.mp inside with occupied | refreshed
    · obtain ⟨t, member, rfl⟩ := List.mem_map.mp occupied
      rcases List.mem_append.mp member with instruction | additional
      · obtain ⟨r, owner, touch⟩ := List.mem_flatMap.mp instruction
        by_cases prior : StateMsg.timeNat r.statePull < time
        · exact ih _ prior r owner rfl t touch
        rcases (localTouches r owner t touch).push_kind with readback | written
        · change Word.isU64 t.2.value
          rw [readback.1]
          exact good
        · change MemoryMsg.timeNat t.2 ≤ _ at byCut
          change MemoryMsg.locOf t.2 = loc at location
          rw [location] at written
          have := read_before_write loc
          omega
      · exact host t additional
    · change Word.isU64 e.2.value
      rw [bumps e refreshed]
      exact good
  have complete (time : ℕ) : Closed time := by
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro row owner eq
      apply localWords row owner
      intro t member
      have edge := in_inventory cpu extra refresh owner member
      have facts := localTouches row owner t member
      let loc := MemoryMsg.locOf t.2
      have order : MemoryMsg.timeNat t.1.1 < MemoryMsg.timeNat t.2 := rank (e := (t.1.1, t.2)) edge
      have early := prior_in_read_window (t := t) facts order
      rw [← facts.loc_eq, eq] at early
      exact (prefixAt loc _ (before time ih loc)).1 (t.1.1, t.2) (List.mem_filter.mpr ⟨edge, by simp [loc]⟩) early
  have renew (e : Pair p) (member : e ∈ edges) (good : MemoryMsg.isU64 e.1) : MemoryMsg.isU64 e.2 := by
    rcases List.mem_append.mp member with occupied | refreshed
    · obtain ⟨t, present, rfl⟩ := List.mem_map.mp occupied
      rcases List.mem_append.mp present with instruction | additional
      · obtain ⟨r, owner, inside⟩ := List.mem_flatMap.mp instruction
        exact complete _ r owner rfl t inside
      · exact host t additional
    · change Word.isU64 e.2.value
      rw [bumps e refreshed]
      exact good
  have all (loc : MemLoc) (time : ℕ) := prefixAt loc time (fun e mem _ => renew e (List.mem_filter.mp mem).1)
  exact ⟨fun e member => (all (MemoryMsg.locOf e.2) _).1 e (List.mem_filter.mpr ⟨member, by simp⟩) le_rfl,
    fun loc m present => (all loc _).2 m present le_rfl⟩

end SP1Clean.Soundness.MemoryRecordChain
