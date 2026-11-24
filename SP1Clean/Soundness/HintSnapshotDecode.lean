import SP1Clean.Proofs.Operations.HintSnapshotPositions
import SP1Clean.Soundness.HintSnapshotOrder

/-! # Recovering outgoing hint bytes from the ordered immutable reads

A public buffer may span many words. The cursor carries the same private head and tail
at each interior position. The first node lookup and every word lookup, including the
final padded word, therefore identify the exact buffer in the persistent store.
-/

namespace SP1Clean.HostHintSnapshot

open Circuit Air.Flat Semantics Semantics.HintQueue Soundness Soundness.Target
variable {p : ℕ} [Fact p.Prime]

private theorem first_cursor {R V : Type*} {edge : R → V × V} {start stop : V} {rows : List R}
    (walk : Walk.IsWalk edge start stop rows) (live : 0 < rows.length) : (edge rows[0]).1 = start := by
  cases rows with
  | nil => contradiction
  | cons => exact walk.1

private theorem next_cursor {R V : Type*} {edge : R → V × V} {start stop : V} {rows : List R}
    (walk : Walk.IsWalk edge start stop rows) (i : ℕ) (live : i < rows.length) :
    (edge rows[i]).2 = if more : i + 1 < rows.length then (edge rows[i+1]).1 else stop := by
  induction rows generalizing start i with
  | nil => contradiction
  | cons r rest ih =>
    cases i with
    | zero =>
      cases rest with
      | nil => exact walk.2
      | cons => exact walk.2.1.symm
    | succ i =>
      have previous := ih walk.2 i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using live)
      by_cases more : i + 1 < rest.length <;> simpa [more] using previous

/-- The incoming and outgoing cursor messages carried by decoded row cells. -/
def inputEdge (r : Inputs (ZMod p)) : Cursor (ZMod p) × Cursor (ZMod p) := (r.1.before r.2.1, r.1.after r.2.1)

/-- Exactly the immutable lookups demanded by this row and their shared persistent store. -/
def BoundReads (store : Store) (r : Inputs (ZMod p)) : Prop :=
  (r.1.first = 1 → (r.1.node r.2.1).Valid ∧ (r.1.node r.2.1).Binds store) ∧
    (r.1.active = 1 → (r.1.word r.2.1).Binds store)

private theorem buffer_reads [Fact (2 ^ 17 < p)] (store : Store) (start : ℕ) (bytes : Bytes)
    (rows : List (Inputs (ZMod p))) (init stop : Cursor (ZMod p))
    (scheduled : rows.map Prod.fst = bufferShapes start bytes)
    (walk : Walk.IsWalk inputEdge init stop rows) (auth : ∀ r ∈ rows, BoundReads store r) :
    let head := Address.toNat init.head
    let tail := Address.toNat stop.head
    head < 2 ^ 48 ∧ tail < head ∧ ReadsNode p store head tail bytes := by
  have count : rows.length = wordCount bytes := by
    simpa only [List.length_map, bufferShapes, List.length_range, List.size_toArray, wordCount] using
      congrArg List.length scheduled
  have positive : 0 < rows.length := count ▸ wordCount_pos bytes
  let first := rows[0]
  let links := first.2.1
  have entry (i : ℕ) (hi : i < rows.length) :
      rows[i].1 = shape (start + i) i bytes.length (arrayWord bytes.toArray i) := by
    have atIndex := List.getElem_of_eq scheduled (i := i) (by simpa using hi)
    simpa [bufferShapes] using atIndex
  have step (i : ℕ) (hi : i < rows.length) :
      inputEdge rows[i] = (position start rows[i].2.1 (wordCount bytes) i,
        position start rows[i].2.1 (wordCount bytes) (i + 1)) := by
    have h := step_positions start rows[i].2.1 bytes.length i (arrayWord bytes.toArray i) (by change i < wordCount bytes; omega)
    exact Prod.ext (by simpa only [wordCount, inputEdge, entry i hi] using h.1) (by simpa only [wordCount, inputEdge, entry i hi] using h.2)
  have stable (i : ℕ) (hi : i < rows.length) : rows[i].2.1 = links := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have prev : i < rows.length := by omega
      have same := next_cursor walk i prev
      rw [dite_eq_left hi, step i prev, step (i + 1) hi] at same
      have inner : i + 1 < wordCount bytes := count ▸ hi
      have heads := congrArg Cursor.head same
      have tails := congrArg Cursor.tail same
      simp only [position, Nat.ne_of_lt inner, ite_false, Nat.zero_lt_succ, inner, and_self, ite_true] at heads tails
      have equal : rows[i].2.1 = rows[i+1].2.1 := by
        cases h : rows[i].2.1
        cases k : rows[i+1].2.1
        simp only [h, k] at heads tails
        congr
      exact equal.symm.trans (ih prev)
  have front := first_cursor walk positive
  rw [step 0 positive] at front
  have frontHead := congrArg Cursor.head front
  simp only [position, Nat.ne_of_lt (wordCount_pos bytes), ite_false] at frontHead
  let j := rows.length - 1
  have endIndex : j < rows.length := by dsimp [j]; omega
  have last : j + 1 = rows.length := by dsimp [j]; omega
  have back := next_cursor walk j endIndex
  rw [dite_eq_right (by omega : ¬ j + 1 < rows.length), step j endIndex, stable j endIndex, last, count] at back
  have backHead := congrArg Cursor.head back
  simp only [position, ite_true] at backHead
  have metadata := (auth first (List.getElem_mem positive)).1 (by simp [first, entry 0 positive, shape])
  have firstRecord : first.1.node links = (⟨links.head, links.tail, bitVecToWord (BitVec.ofNat 64 bytes.length)⟩ : NodeRecord (ZMod p)) := by
    unfold Shape.node
    simp [first, entry 0 positive, shape]
  change links.head = init.head at frontHead
  change links.tail = stop.head at backHead
  rw [← frontHead, ← backHead]
  change (first.1.node links).Valid ∧ (first.1.node links).Binds store at metadata
  rw [firstRecord] at metadata
  obtain ⟨⟨headBound, tailBound, down, _⟩, node⟩ := metadata
  change Address.Bounded links.head at headBound
  change Address.Bounded links.tail at tailBound
  refine ⟨Address.toNat_lt headBound, down, ?_, ?_⟩
  · simpa only [NodeRecord.encode, Address.ofNat_toNat headBound, Address.ofNat_toNat tailBound] using node
  · intro i hi
    have inRows : i < rows.length := count ▸ hi
    have word := (auth _ (List.getElem_mem inRows)).2 (by simp [entry i inRows, shape])
    have finalFlag : (i = bytes.length / 8) ↔ i + 1 = wordCount bytes := by simp [wordCount]
    simpa only [Shape.word, entry i inRows, shape, stable i inRows, arrayWord_toArray,
      WordRecord.encode, Address.ofNat_toNat headBound, finalFlag] using word

/-- Reading the ordered public shapes from one authenticated store reconstructs the entire
outgoing queue, including the empty-queue case and the last padded word of each buffer. -/
theorem walk_reads_snapshot [Fact (2 ^ 17 < p)] (store : Store) (start : ℕ) (hints : List Bytes)
    (rows : List (Inputs (ZMod p))) (init stop : Cursor (ZMod p))
    (scheduled : rows.map Prod.fst = shapesFrom start hints)
    (walk : Walk.IsWalk inputEdge init stop rows) (auth : ∀ r ∈ rows, BoundReads store r)
    (width : wordRows hints < 2 ^ 48) (nul : stop.head = 0) :
    ∃ tails, ReadsSnapshot p store (Address.toNat init.head) hints tails := by
  induction hints generalizing start rows init with
  | nil =>
    have empty : rows = [] := List.map_eq_nil_iff.mp scheduled
    subst rows
    change init = stop at walk
    refine ⟨[], ?_⟩
    change Address.toNat init.head = 0
    rw [walk, nul, ← Address.ofNat_zero, Address.toNat_ofNat _ (by decide)]
  | cons bytes rest ih =>
    let n := wordCount bytes
    have firstLength : (bufferShapes (p := p) start bytes).length = n := by simp [bufferShapes, n, wordCount]
    change _ = bufferShapes start bytes ++ shapesFrom (start + n) rest at scheduled
    have left : (rows.take n).map Prod.fst = bufferShapes start bytes := by
      rw [List.map_take, scheduled, ← firstLength, List.take_left]
    have right : (rows.drop n).map Prod.fst = shapesFrom (start + n) rest := by
      rw [List.map_drop, scheduled, ← firstLength, List.drop_left, firstLength]
    obtain ⟨middle, firstWalk, suffix⟩ := (Walk.isWalk_append inputEdge (rows.take n) (rows.drop n) init stop).mp
      (by simpa only [List.take_append_drop] using walk)
    have node := buffer_reads store start bytes _ _ _ left firstWalk (fun r m => auth r (List.mem_of_mem_take m))
    have size : wordCount bytes + wordRows rest < 2 ^ 48 := width
    obtain ⟨tails, chain⟩ := ih (start + n) (rows.drop n) middle right suffix
      (fun r m => auth r (List.mem_of_mem_drop m)) (by omega)
    exact ⟨Address.toNat middle.head :: tails, node.1, node.2.1, by omega, node.2.2, chain⟩

/-- The signed walk visits exactly the publicly scheduled shapes at their genuine row environments. -/
private theorem public_shapes (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints)
    (fit : fits hints = true) :
    (((List.finRange t.table.length).take (wordRows hints)).map (physicalInput t)).map Prod.fst = shapesFrom 0 hints := by
  have height := physical_height hints t same
  have capacity : wordRows hints ≤ t.table.length := by
    rw [height]
    simpa only [inventory, StaticTable.ofRows, schedule_length, fit, ↓reduceIte] using (inventory (p := p) hints).length_le_height
  apply List.ext_getElem
  · simp [capacity, shapesFrom_length]
  · intro i ha hb
    have live : i < wordRows hints := shapesFrom_length (p := p) 0 hints ▸ hb
    have index : i < t.table.length := live.trans_le capacity
    have eq := physical_shape hints t same ⟨i, index⟩
    simp only [List.getElem_map, List.getElem_take, List.getElem_finRange]
    change (valueFromOffset Inputs 0 (t.environment t.table[i])).1 = _
    rw [eq]
    simp only [fixedShapes, Vector.getElem_ofFn, List.getElem?_toArray, schedule, fit, ↓reduceIte,
      List.getElem?_eq_getElem hb, Option.getD_some]

/-- The ordered physical walk determines the complete target queue in any persistent
store authenticating its actual node and word requests. -/
theorem reads_snapshot_of_walk [Fact (2 ^ 17 < p)] (store : Store) (hints : List Bytes)
    (t : Table (ZMod p)) (same : t.component = component hints) (checked : t.Constraints) (head : fields 3 (ZMod p))
    (walk : Walk.IsWalk (physicalEdge t) (endpoint 0 head) (endpoint (wordRows hints) 0)
      ((List.finRange t.table.length).take (wordRows hints)))
    (reads : ∀ i : Fin t.table.length, i.val < wordRows hints → BoundReads store (physicalInput t i)) :
    ∃ tails, ReadsSnapshot p store (Address.toNat head) hints tails := by
  have positive : 0 < t.table.length := physical_height hints t same ▸ (inventory (p := p) hints).height_pos
  have fit := (count_of_constraints hints _ (same ▸ checked _ (List.getElem_mem positive))).1
  apply walk_reads_snapshot store 0 hints _ _ _ (public_shapes hints t same fit)
    ((Walk.isWalk_map inputEdge (physicalInput t) _ _ _).mpr walk) _ (of_decide_eq_true fit) rfl
  intro r member
  obtain ⟨i, inPrefix, rfl⟩ := List.mem_map.mp member
  apply reads i
  have kept : i ∈ (List.finRange t.table.length).take (wordRows hints) := inPrefix
  obtain ⟨j, hj, atRow⟩ := List.getElem_of_mem kept
  have bound : j < wordRows hints := Nat.lt_of_lt_of_le hj (List.length_take_le ..)
  rw [← atRow]
  simpa only [List.getElem_take, List.getElem_finRange, Fin.val_cast] using bound

end SP1Clean.HostHintSnapshot
