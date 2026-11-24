import SP1Clean.Soundness.AllocationWordBytes
import SP1Clean.Soundness.Walk

/-! # The byte semantics of a complete immutable allocation-word walk -/

namespace SP1Clean.WriteAllocation.Words
open Semantics Semantics.HintQueue Soundness
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq

/-- A full physical word publishes its next cursor. A partial or empty physical word ends
its walk; no physical word can consume the resulting terminal marker. -/
def wordEdge (r : Row F) : Option (Cursor F) × Option (Cursor F) :=
  (some r.prior, if r.payload.more = 1 then some r.next else none)

private theorem count_more (remaining next count : Nat) (full : 8 ≤ remaining)
    (less : next = remaining - 8) (size : count = next / 8 + 1) :
    count + 1 = remaining / 8 + 1 := by omega

private theorem count_last (remaining : Nat) (short : ¬ 8 ≤ remaining) :
    1 = remaining / 8 + 1 := by omega

private theorem step_index (idx base next i : Nat) (h : idx = next + i) (inc : next = base + 1) :
    idx = base + (i+1) := by omega

private theorem step_remaining (rem base next i : Nat) (h : rem = next - (8 * i)) (less : next = base - 8) :
    rem = base - (8 * (i+1)) := by omega

private theorem at_cursor {rows : List (Row F)} {initial : Cursor F}
    (walk : Walk.IsWalk wordEdge (some initial) none rows) (checked : ∀ r ∈ rows, r.Valid) :
    rows.length = Address.toNat initial.remaining / 8 + 1 ∧
    ∀ i : Fin rows.length, let r := rows[i.val]
      r.Valid ∧ r.prior.contents = initial.contents ∧
      Address.toNat r.prior.index = Address.toNat initial.index + i.val ∧
      Address.toNat r.prior.remaining = Address.toNat initial.remaining - (8 * i.val) := by
  induction rows generalizing initial with
  | nil => change (some initial : Option _) = none at walk; contradiction
  | cons r rs ih =>
    obtain ⟨same,walk⟩ := walk
    have same : r.prior = initial := Option.some.inj same
    subst initial
    have v := checked r List.mem_cons_self
    have bounds := v.bounds
    by_cases more : r.payload.more = 1
    · have nextWalk : Walk.IsWalk wordEdge (some r.next) none rs := by simpa only [wordEdge,more,ite_true] using walk
      obtain ⟨count,positions⟩ := ih nextWalk (fun x m => checked x (List.mem_cons_of_mem r m))
      have enough := bounds.2.2.1.mp more
      have less : Address.toNat r.next.remaining = Address.toNat r.prior.remaining - 8 := bounds.2.1
      have increment := v.2.2.2.1.2.2.2
      change Address.toNat r.next.index = Address.toNat r.prior.index + Address.toNat (#v[1,0,0] : fields 3 F) at increment
      rw [show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at increment
      refine ⟨count_more _ _ _ enough less count,?_⟩
      rintro ⟨i,hi⟩
      cases i with
      | zero => exact ⟨v,rfl,by simp,by simp⟩
      | succ i =>
        have inside : i < rs.length := by simpa using hi
        obtain ⟨valid,owner,idx,remains⟩ := positions ⟨i,inside⟩
        change Address.toNat rs[i].prior.index = Address.toNat r.next.index + i at idx
        change Address.toNat rs[i].prior.remaining = Address.toNat r.next.remaining - (8 * i) at remains
        exact ⟨valid,owner,step_index _ _ _ i idx increment,step_remaining _ _ _ i remains less⟩
    · have stopped : Walk.IsWalk wordEdge none none rs := by simpa only [wordEdge,ite_eq_right more] using walk
      have short := mt bounds.2.2.1.mpr more
      cases rs with
      | nil =>
        refine ⟨count_last _ short,?_⟩
        rintro ⟨i, hi⟩
        have zero := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
        subst i
        exact ⟨v,rfl,by simp,by simp⟩
      | cons other tail =>
        have missing : some other.prior = none := stopped.1
        contradiction

/-- An exhaustive walk from a node's physical seed determines its full byte buffer and the
canonical record backed by every participating word row. -/
theorem decode_walk (c : Contents F) (rows : List (Row F))
    (walk : Walk.IsWalk wordEdge (some (start c)) none rows) (checked : ∀ r ∈ rows, r.Valid) :
    (decodedBytes c rows).length = Address.toNat c.length ∧
    ∀ r ∈ rows, r.word ∈ nodeWordRows (p := SP1Prime) (Address.toNat c.pointer) (decodedBytes c rows) := by
  obtain ⟨size,pos⟩ := at_cursor walk checked
  refine decode_records c rows size ?_
  intro i
  obtain ⟨valid,owner,idx,rem⟩ := pos i
  have zero : Address.toNat (start c).index = 0 := by change Address.toNat (0 : fields 3 F) = 0; decide
  exact ⟨valid,owner,by rwa [zero,Nat.zero_add] at idx,rem⟩

private theorem final_short (length : Nat) : ¬ 8 ≤ length - (8 * (length / 8)) := by omega

/-- Every word position occurs at its physical index and pointer. The final position has a
unit last marker, including when it is the empty word of an aligned or empty buffer. -/
theorem walk_inventory (c : Contents F) (rows : List (Row F))
    (walk : Walk.IsWalk wordEdge (some (start c)) none rows) (checked : ∀ r ∈ rows, r.Valid) :
    (∀ i : Fin rows.length, let r := rows[i.val]
      r.word.pointer = c.pointer ∧ Address.toNat r.word.index = i.val) ∧
    ∃ last ∈ rows, last.word.pointer = c.pointer ∧ Address.toNat last.word.index + 1 = rows.length ∧
      last.word.isLast = 1 := by
  obtain ⟨size,pos⟩ := at_cursor walk checked
  change rows.length = Address.toNat c.length / 8 + 1 at size
  have zero : Address.toNat (start c).index = 0 := by change Address.toNat (0 : fields 3 F) = 0; decide
  have indices (i : Fin rows.length) : let r := rows[i.val]
      r.word.pointer = c.pointer ∧ Address.toNat r.word.index = i.val := by
    obtain ⟨_,owner,index,_⟩ := pos i
    exact ⟨congrArg Contents.pointer owner,by rwa [zero,Nat.zero_add] at index⟩
  refine ⟨indices,?_⟩
  let i : Fin rows.length := ⟨Address.toNat c.length / 8,by rw [size]; exact Nat.lt_succ_self _⟩
  let last := rows[i.val]
  obtain ⟨stored,index⟩ := indices i
  obtain ⟨valid,_,_,remaining⟩ := pos i
  change Address.toNat last.prior.remaining = Address.toNat c.length - (8 * (Address.toNat c.length / 8)) at remaining
  have short : ¬8 ≤ Address.toNat last.prior.remaining := by rw [remaining]; exact final_short _
  have stopped := mt valid.bounds.2.2.1.mp short
  have flag : last.payload.more = 0 := ((valid.2.1 (7 : Fin 8)).2.1).resolve_right stopped
  refine ⟨last,List.getElem_mem i.isLt,stored,(congrArg (· + 1) index).trans size.symm,?_⟩
  change 1-last.payload.more = 1
  rw [flag,sub_zero]

private theorem length_eq {x y : Nat} (left : x < 2^51) (right : y < 2^51)
    (same : BitVec.ofNat 64 x = BitVec.ofNat 64 y) : x = y := by
  have eq := congrArg BitVec.toNat same
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show x < 2^64 by omega),
    Nat.mod_eq_of_lt (show y < 2^64 by omega)] using eq

private theorem node_eq {a b : Node} (bytes : a.bytes = b.bytes) (tail : a.tail = b.tail) : a = b := by
  cases a; cases b
  exact congrArg₂ Node.mk bytes tail

private theorem words_eq {rows : List (Row F)} {pointer : fields 3 F} {a b : Store} {na nb : Node}
    (atA : node? a (Address.toNat pointer) = some na) (atB : node? b (Address.toNat pointer) = some nb)
    (len : na.bytes.length = nb.bytes.length) (count : rows.length = wordCount na.bytes)
    (positions : ∀ i : Fin rows.length, let r := rows[i.val]
      r.word.pointer = pointer ∧ Address.toNat r.word.index = i.val)
    (words : ∀ r ∈ rows, r.word.Binds a ∧ r.word.Binds b) : na.bytes = nb.bytes := by
  apply bytes_eq_of_words len
  intro index bound
  have inRows : index < rows.length := by rwa [count]
  let r := rows[index]
  obtain ⟨ptr,idx⟩ := positions ⟨index,inRows⟩
  obtain ⟨ba,bb⟩ := words r (List.getElem_mem inRows)
  have hereA : node? a (Address.toNat r.word.pointer) = some na := by rw [ptr]; exact atA
  have hereB : node? b (Address.toNat r.word.pointer) = some nb := by rw [ptr]; exact atB
  have equal := (ba.value hereA).2.symm.trans (bb.value hereB).2
  change Address.toNat r.word.index = index at idx
  exact (congrArg (wordValue na.bytes) idx.symm).trans (equal.trans (congrArg (wordValue nb.bytes) idx))

/-- Any two stores authenticating one metadata row and its entire physical word walk agree
on the actual node. The terminal word bounds the true lengths before four-limb comparison. -/
theorem walk_determines_node (c : Contents F) (metadata : NodeRecord F) (linked : c.pointer = metadata.pointer)
    {rows : List (Row F)} (walk : Walk.IsWalk wordEdge (some (start c)) none rows)
    (checked : ∀ r ∈ rows, r.Valid) {a b : Store} (ma : metadata.Binds a) (mb : metadata.Binds b)
    (words : ∀ r ∈ rows, r.word.Binds a ∧ r.word.Binds b) :
    node? a (Address.toNat metadata.pointer) = node? b (Address.toNat metadata.pointer) := by
  obtain ⟨positions,last,member,pointer,number,ended⟩ := walk_inventory c rows walk checked
  obtain ⟨na,atA,tailA,lengthA⟩ := ma
  obtain ⟨nb,atB,tailB,lengthB⟩ := mb
  have terminalA : node? a (Address.toNat last.word.pointer) = some na := by rw [pointer,linked]; exact atA
  have terminalB : node? b (Address.toNat last.word.pointer) = some nb := by rw [pointer,linked]; exact atB
  obtain ⟨finalA,finalB⟩ := words last member
  have lastOK := (checked last member).word_valid
  have boundedA := finalA.length_bound_of_last lastOK terminalA ended
  have boundedB := finalB.length_bound_of_last lastOK terminalB ended
  have len := length_eq boundedA boundedB (lengthA.symm.trans lengthB)
  have count := number.symm.trans ((finalA.isLast_iff terminalA).mp ended)
  rw [linked] at positions
  have contents := words_eq atA atB len count positions words
  exact atA.trans ((congrArg some (node_eq contents (tailA.symm.trans tailB))).trans atB.symm)

end SP1Clean.WriteAllocation.Words
