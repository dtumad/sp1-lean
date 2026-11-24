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

end SP1Clean.WriteAllocation.Words
