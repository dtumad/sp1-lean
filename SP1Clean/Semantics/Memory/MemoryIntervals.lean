module

public import SP1Clean.Semantics.Memory.MemorySupport
public import Mathlib.Data.Finset.Sort

/-! # Maximal constant-byte runs of bounded sparse memory

Only a nonzero byte or its immediate successor can begin a new run. Sort the finite set of
actual value changes and emit one half-open row between consecutive boundaries. This represents
the complete address space, including zero-filled gaps, without visiting every address.
-/

@[expose] public section

namespace SP1Clean.Semantics

/-- A constant byte value on a half-open address interval. -/
structure MemoryInterval where
  lower : ℕ
  upper : ℕ
  value : BitVec 8
deriving DecidableEq, Repr

namespace MemoryInterval

def Contains (interval : MemoryInterval) (address : ℕ) : Prop :=
  interval.lower ≤ address ∧ address < interval.upper

instance (interval : MemoryInterval) (address : ℕ) : Decidable (interval.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

end MemoryInterval

namespace ByteMemory

/-- Interior boundaries at which the represented byte changes. The finite candidate set
includes each live address and the address immediately following it. -/
def changePoints (memory : ByteMemory) (limit : ℕ) : Finset ℕ :=
  let live := memory.supportBelow limit
  (live ∪ live.image Nat.succ).filter fun a =>
    0 < a ∧ a < limit ∧ memory.read (a - 1) ≠ memory.read a

@[simp] theorem mem_changePoints (memory : ByteMemory) (limit address : ℕ) :
    address ∈ memory.changePoints limit ↔
      0 < address ∧ address < limit ∧ memory.read (address - 1) ≠ memory.read address := by
  rw [changePoints, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  by_cases live : memory.read address = 0
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨address - 1, ?_, by omega⟩)
    refine (mem_supportBelow ..).mpr ⟨by omega, ?_⟩
    exact fun zero => h.2.2 (zero.trans live.symm)
  · exact Finset.mem_union_left _ ((mem_supportBelow ..).mpr ⟨h.2.1, live⟩)

/-- One live byte contributes at most two potential run boundaries. -/
theorem changePoints_card_le (memory : ByteMemory) (limit : ℕ) :
    (memory.changePoints limit).card ≤ 2 * (memory.supportBelow limit).card := by
  let live := memory.supportBelow limit
  calc
    _ ≤ (live ∪ live.image Nat.succ).card := Finset.card_filter_le ..
    _ ≤ live.card + (live.image Nat.succ).card := Finset.card_union_le ..
    _ ≤ 2 * live.card := by have h : (live.image Nat.succ).card ≤ live.card := Finset.card_image_le; omega

/-- Emit one row for each consecutive pair of boundaries, ending at the public limit. -/
private def runRows (read : ℕ → BitVec 8) (limit lower : ℕ) : List ℕ → List MemoryInterval
  | [] => if lower < limit then [⟨lower, limit, read lower⟩] else []
  | next :: rest => ⟨lower, next, read lower⟩ :: runRows read limit next rest

private theorem runRows_length (read : ℕ → BitVec 8) (limit lower : ℕ) (cuts : List ℕ)
    (ordered : (lower :: cuts).Pairwise (· < ·)) (bounded : ∀ n ∈ cuts, n < limit) :
    (runRows read limit lower cuts).length = cuts.length + if lower < limit then 1 else 0 := by
  induction cuts generalizing lower with
  | nil => simp only [runRows, List.length_nil, Nat.zero_add]; split <;> rfl
  | cons next rest ih =>
    have low := (List.pairwise_cons.mp ordered).1 next (by simp)
    have hi := bounded next (by simp)
    simp [runRows, ih next (List.pairwise_cons.mp ordered).2 (fun n hn => bounded n (List.mem_cons_of_mem _ hn)),
      hi, low.trans hi, Nat.add_assoc]

private theorem runRows_bounds (read : ℕ → BitVec 8) (limit lower : ℕ) (cuts : List ℕ)
    (ordered : (lower :: cuts).Pairwise (· < ·)) (bounded : ∀ n ∈ cuts, n < limit)
    (row : MemoryInterval) (member : row ∈ runRows read limit lower cuts) :
    lower ≤ row.lower ∧ row.lower < row.upper ∧ row.upper ≤ limit ∧ row.value = read row.lower ∧
    (row.upper = limit ∨ row.upper ∈ cuts) ∧
    ∀ n ∈ cuts, ¬ (row.lower < n ∧ n < row.upper) := by
  induction cuts generalizing lower with
  | nil =>
    simp only [runRows] at member
    split at member
    · obtain rfl := List.mem_singleton.mp member
      simp_all
    · simp at member
  | cons next rest ih =>
    have first := (List.pairwise_cons.mp ordered).1 next (by simp)
    have tail := (List.pairwise_cons.mp ordered).2
    have nextBound := bounded next (by simp)
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨le_rfl, first, nextBound.le, rfl, Or.inr (by simp), ?_⟩
      intro n hn between
      rcases List.mem_cons.mp hn with rfl | hn
      · exact (lt_irrefl _) between.2
      · exact (lt_asymm between.2) ((List.pairwise_cons.mp tail).1 _ hn)
    · obtain ⟨lo, nonempty, hi, value, upper, absent⟩ :=
        ih next tail (fun n hn => bounded n (List.mem_cons_of_mem _ hn)) later
      refine ⟨first.le.trans lo, nonempty, hi, value,
        upper.imp_right (List.mem_cons_of_mem _), ?_⟩
      intro n hn between
      rcases List.mem_cons.mp hn with rfl | hn
      · omega
      · exact absent n hn between

private theorem runRows_count (read : ℕ → BitVec 8) (limit lower query : ℕ) (cuts : List ℕ)
    (ordered : (lower :: cuts).Pairwise (· < ·)) (bounded : ∀ n ∈ cuts, n < limit) :
    (runRows read limit lower cuts).countP (fun row => decide (row.Contains query)) =
      if lower ≤ query ∧ query < limit then 1 else 0 := by
  have indicator (lo hi : ℕ) :
      (if decide ((MemoryInterval.mk lo hi (read lo)).Contains query) then (1 : ℕ) else 0) =
        if lo ≤ query ∧ query < hi then 1 else 0 := by
    change (if decide (lo ≤ query ∧ query < hi) = true then 1 else 0) = _
    split
    · next h => exact (ite_eq_left (of_decide_eq_true h)).symm
    · next h => exact (ite_eq_right (fun inside => h (decide_eq_true inside))).symm
  induction cuts generalizing lower with
  | nil =>
    rw [runRows]
    split
    · rw [List.countP_cons, List.countP_nil, Nat.zero_add, indicator]
    · simp only [List.countP_nil]
      rw [ite_eq_right (by omega)]
  | cons next rest ih =>
    have first := (List.pairwise_cons.mp ordered).1 next (by simp)
    have hi := bounded next (by simp)
    rw [runRows, List.countP_cons, ih next (List.pairwise_cons.mp ordered).2 (fun n hn => bounded n (List.mem_cons_of_mem _ hn)), indicator]
    split_ifs <;> omega

/-- The canonical nonempty maximal runs, ordered by increasing address. -/
@[no_expose] def intervals (memory : ByteMemory) (limit : ℕ) : List MemoryInterval :=
  runRows memory.read limit 0 (memory.changePoints limit).sort

private theorem cuts_ordered (memory : ByteMemory) (limit : ℕ) :
    (0 :: (memory.changePoints limit).sort).Pairwise (· < ·) := by
  refine List.pairwise_cons.mpr ⟨?_, (memory.changePoints limit).sortedLT_sort.pairwise⟩
  intro n hn
  exact ((mem_changePoints ..).mp ((Finset.mem_sort _).mp hn)).1

private theorem cuts_bounded (memory : ByteMemory) (limit : ℕ) :
    ∀ n ∈ (memory.changePoints limit).sort, n < limit :=
  fun _ hn => ((mem_changePoints ..).mp ((Finset.mem_sort _).mp hn)).2.1

/-- Two snapshots that agree throughout the address window generate identical ordered rows,
including all zero-filled gaps. -/
theorem intervals_congr {left right : ByteMemory} {limit : ℕ}
    (same : left.agreesBelow right limit = true) : left.intervals limit = right.intervals limit := by
  have reads := (agreesBelow_iff left right limit).mp same
  have cuts : left.changePoints limit = right.changePoints limit := by
    ext a
    simp only [mem_changePoints]
    by_cases h : a < limit
    · rw [reads a h, reads (a - 1) (by omega)]
    · simp [h]
  rw [intervals, intervals, cuts]
  have rows (lower : ℕ) (points : List ℕ) (bounded : ∀ a ∈ points, a < limit)
      (lo : lower < limit) : runRows left.read limit lower points = runRows right.read limit lower points := by
    induction points generalizing lower with
    | nil => simp [runRows, reads lower lo]
    | cons next rest ih =>
      rw [runRows, runRows, reads lower lo, ih next (fun a ha => bounded a (List.mem_cons_of_mem _ ha))
        (bounded next (by simp))]
  by_cases positive : 0 < limit
  · exact rows _ _ (cuts_bounded right limit) positive
  · obtain rfl : limit = 0 := by omega
    have empty : right.changePoints 0 = ∅ := by ext; simp
    simp [empty, runRows]

/-- Every bounded address belongs to exactly one row. -/
theorem intervals_count (memory : ByteMemory) (limit query : ℕ) :
    (memory.intervals limit).countP (fun interval => decide (interval.Contains query)) =
      if query < limit then 1 else 0 := by
  simpa [intervals] using runRows_count memory.read limit 0 query _ (cuts_ordered memory limit) (cuts_bounded memory limit)

/-- The row count is exactly one per maximal run in a nonempty address window. -/
theorem intervals_length (memory : ByteMemory) (limit : ℕ) :
    (memory.intervals limit).length = (memory.changePoints limit).card + if 0 < limit then 1 else 0 := by
  simpa [intervals] using runRows_length memory.read limit 0 _ (cuts_ordered memory limit) (cuts_bounded memory limit)

/-- The sparse support bounds the number of runs even when every live byte is isolated. -/
theorem intervals_length_le (memory : ByteMemory) (limit : ℕ) :
    (memory.intervals limit).length ≤ 2 * (memory.supportBelow limit).card + 1 := by
  rw [intervals_length]
  have := memory.changePoints_card_le limit
  split <;> omega

/-- Any complete list of sound constant-byte intervals has at least as many rows as
the canonical list. Each actual change forces a distinct lower endpoint. -/
theorem intervals_length_minimal (memory : ByteMemory) (limit : ℕ) (rows : List MemoryInterval)
    (cover : ∀ address < limit, ∃ row ∈ rows, row.Contains address)
    (sound : ∀ row ∈ rows, ∀ address, row.Contains address → memory.read address = row.value) :
    (memory.intervals limit).length ≤ rows.length := by
  rw [intervals_length]
  by_cases positive : 0 < limit
  · rw [ite_eq_left positive]
    have begins : insert 0 (memory.changePoints limit) ⊆ (rows.map MemoryInterval.lower).toFinset := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | change
      · obtain ⟨row, member, lo, _⟩ := cover 0 positive
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, member, Nat.eq_zero_of_le_zero lo⟩)
      · have h := (mem_changePoints ..).mp change
        obtain ⟨row, member, lo, hi⟩ := cover a h.2.1
        have starts : row.lower = a := by
          by_contra different
          apply h.2.2
          exact (sound row member (a - 1) ⟨by omega, by omega⟩).trans (sound row member a ⟨lo, hi⟩).symm
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, member, starts⟩)
    have lower := Finset.card_le_card begins
    rw [Finset.card_insert_of_notMem (by simp)] at lower
    simpa only [List.length_map] using lower.trans (List.toFinset_card_le _)
  · obtain rfl : limit = 0 := by omega
    have noCuts : memory.changePoints 0 = ∅ := by ext; simp
    simp [noCuts]

/-- Each fixed row covers a nonempty part of the bounded address space. -/
theorem intervals_nonempty (memory : ByteMemory) (limit : ℕ) (row : MemoryInterval)
    (member : row ∈ memory.intervals limit) : row.lower < row.upper ∧ row.upper ≤ limit := by
  have h := runRows_bounds memory.read limit 0 _ (cuts_ordered memory limit) (cuts_bounded memory limit) row member
  exact ⟨h.2.1, h.2.2.1⟩

theorem intervals_bounds (memory : ByteMemory) (limit : ℕ) (row : MemoryInterval)
    (member : row ∈ memory.intervals limit) : row.lower ≤ row.upper ∧ row.upper ≤ limit :=
  (intervals_nonempty memory limit row member).imp_left Nat.le_of_lt

/-- The original byte is constant throughout every emitted row. -/
theorem intervals_sound (memory : ByteMemory) (limit : ℕ) (row : MemoryInterval)
    (member : row ∈ memory.intervals limit) (query : ℕ) (inside : row.Contains query) :
    query < limit ∧ memory.read query = row.value := by
  obtain ⟨_, _, hi, value, _, absent⟩ :=
    runRows_bounds memory.read limit 0 _ (cuts_ordered memory limit) (cuts_bounded memory limit) row member
  refine ⟨inside.2.trans_le hi, ?_⟩
  obtain ⟨lo, lt⟩ := inside
  induction query, lo using Nat.le_induction with
  | base => exact value.symm
  | succ q low ih =>
    have unchanged : memory.read q = memory.read (q + 1) := by
      by_contra differs
      apply absent (q + 1) ((Finset.mem_sort _).mpr ((mem_changePoints ..).mpr ⟨by omega, by omega, by simpa using differs⟩))
      exact ⟨by omega, lt⟩
    exact unchanged.symm.trans (ih (by omega))

/-- An in-range byte has its own authenticated fixed row. -/
theorem intervals_complete (memory : ByteMemory) (limit query : ℕ) (inside : query < limit) :
    ∃ interval ∈ memory.intervals limit, interval.Contains query := by
  by_contra! none
  have empty : (memory.intervals limit).countP (fun row => decide (row.Contains query)) = 0 :=
    List.countP_eq_zero.mpr (fun row hr => by simpa using none row hr)
  rw [intervals_count, ite_eq_left inside] at empty
  contradiction

/-- A zero run ends either at the public limit or at a live byte. -/
theorem intervals_zero_upper (memory : ByteMemory) (limit : ℕ) (row : MemoryInterval)
    (member : row ∈ memory.intervals limit) (zero : row.value = 0) :
    row.upper = limit ∨ row.upper ∈ memory.supportBelow limit := by
  obtain ⟨_, lo, _, _, upper, _⟩ :=
    runRows_bounds memory.read limit 0 _ (cuts_ordered memory limit) (cuts_bounded memory limit) row member
  refine upper.imp_right (fun h => ?_)
  have change := (mem_changePoints ..).mp ((Finset.mem_sort _).mp h)
  have prev := (memory.intervals_sound limit row member (row.upper - 1) ⟨by omega, by omega⟩).2
  exact (mem_supportBelow ..).mpr ⟨change.2.1, fun e => change.2.2 (prev.trans (zero.trans e.symm))⟩

/-- Finite interval lookup characterizes the memory function exactly. -/
theorem intervals_iff (memory : ByteMemory) (limit query : ℕ) (value : BitVec 8) :
    (∃ interval ∈ memory.intervals limit, interval.Contains query ∧ interval.value = value) ↔
      query < limit ∧ memory.read query = value := by
  constructor
  · rintro ⟨interval, member, inside, rfl⟩
    exact memory.intervals_sound limit interval member query inside
  · rintro ⟨inside, valueEq⟩
    obtain ⟨interval, member, contains⟩ := memory.intervals_complete limit query inside
    exact ⟨interval, member, contains,
      (memory.intervals_sound limit interval member query contains).2.symm.trans valueEq⟩

/-- Executable lookup-row selection for the witness compiler. -/
def intervalAt? (memory : ByteMemory) (limit query : ℕ) : Option MemoryInterval :=
  (memory.intervals limit).find? (fun interval => decide (interval.Contains query))

theorem intervalAt?_sound (memory : ByteMemory) (limit query : ℕ) (interval : MemoryInterval)
    (found : memory.intervalAt? limit query = some interval) :
    interval ∈ memory.intervals limit ∧ interval.Contains query ∧
      query < limit ∧ memory.read query = interval.value := by
  have member := List.mem_of_find?_eq_some found
  have contains : interval.Contains query := by simpa using List.find?_some found
  exact ⟨member, contains, memory.intervals_sound limit interval member query contains⟩

/-- The executable selector succeeds exactly on the semantic address window. -/
theorem intervalAt?_isSome_iff (memory : ByteMemory) (limit query : ℕ) :
    (memory.intervalAt? limit query).isSome = true ↔ query < limit := by
  constructor
  · intro present
    obtain ⟨interval, found⟩ := Option.isSome_iff_exists.mp present
    exact (memory.intervalAt?_sound limit query interval found).2.2.1
  · intro inside
    obtain ⟨interval, member, contains⟩ := memory.intervals_complete limit query inside
    cases found : memory.intervalAt? limit query with
    | none =>
        have := List.find?_eq_none.mp found interval member
        simp [contains] at this
    | some interval => rfl

end ByteMemory

end SP1Clean.Semantics
