import SP1Clean.Proofs.Operations.HintRecordPublications

/-! # Persistent storage from a contiguous allocation history

Every fresh node appends its actual buffer and physical tail. Readback covers the entire
store extension, including nodes which a later HINT_READ has already popped.
-/

namespace SP1Clean.WriteAllocation
open Semantics HintQueue
private abbrev F := ZMod SP1Prime

/-- Materialize physically ordered fresh nodes, preserving the permanent incoming identities. -/
def extendStore (base : Store) (rows : List (Step F)) (bytes : Step F → Bytes) : Store :=
  rows.foldl (fun store r => store.push ⟨bytes r,Address.toNat r.node.node.tail⟩) base

/-- At the end of a contiguous allocation history, every row's physical identity names its
exact immutable node. Local allocator checks also preserve well-formedness of every tail. -/
theorem extendStore_records (base : Store) (rows : List (Step F)) (bytes : Step F → Bytes)
    (wf : WellFormed base) (checked : ∀ r ∈ rows, r.Valid)
    (identities : rows.map (fun r => Address.toNat r.node.node.pointer) = List.range' (base.size + 1) rows.length) :
    Extends base (extendStore base rows bytes) ∧ WellFormed (extendStore base rows bytes) ∧
      (extendStore base rows bytes).size = base.size + rows.length ∧
      ∀ r ∈ rows, node? (extendStore base rows bytes) (Address.toNat r.node.node.pointer) =
        some ⟨bytes r,Address.toNat r.node.node.tail⟩ := by
  induction rows generalizing base with
  | nil => exact ⟨Extends.refl _,wf,rfl,by simp⟩
  | cons r rows ih =>
    let n : Node := ⟨bytes r,Address.toNat r.node.node.tail⟩
    have v := (checked r List.mem_cons_self).2.1
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at identities
    obtain ⟨first, rest⟩ := identities
    have tail : n.tail < base.size+1 := by
      change Address.toNat r.node.node.tail < _
      rw [v.2.2.2.1]
      have fresh := v.2.2.2.2.2
      have ordered := v.2.2.1
      omega
    obtain ⟨extension,well,size,found⟩ := ih (base.push n) (wellFormed_push wf n (by omega))
      (fun x m => checked x (List.mem_cons_of_mem r m)) (by simpa only [Array.size_push] using rest)
    refine ⟨(extends_push base n).trans extension, well, ?_, ?_⟩
    · change (extendStore (base.push n) rows bytes).size = _
      simp only [Array.size_push] at size
      simp only [List.length_cons]
      omega
    · intro x member
      rcases List.mem_cons.mp member with rfl | live
      · exact extension _ _ (first ▸ node?_fresh base n)
      · exact found x live

/-- A store extending the fixed incoming memory is uniquely determined by the complete
contiguous set of new nodes and its permanent frontier. -/
theorem store_unique (base : Store) (rows : List (Step F)) (bytes : Step F → Bytes) {left right : Store}
    (identities : rows.map (fun r => Address.toNat r.node.node.pointer) = List.range' (base.size + 1) rows.length)
    (leftExt : Extends base left) (rightExt : Extends base right)
    (leftSize : left.size = base.size + rows.length) (rightSize : right.size = base.size + rows.length)
    (leftRows : ∀ r ∈ rows, node? left (Address.toNat r.node.node.pointer) =
      some ⟨bytes r,Address.toNat r.node.node.tail⟩)
    (rightRows : ∀ r ∈ rows, node? right (Address.toNat r.node.node.pointer) =
      some ⟨bytes r,Address.toNat r.node.node.tail⟩) : left = right := by
  apply Array.ext_getElem?
  intro i
  by_cases old : i < base.size
  · have stored : node? base (i+1) = some base[i] := by simp [node?,old]
    exact (leftExt _ _ stored).trans (rightExt _ _ stored).symm
  by_cases present : i < left.size
  · have required : i+1 ∈ rows.map (fun r => Address.toNat r.node.node.pointer) := by
      rw [identities,List.mem_range'_1]
      omega
    obtain ⟨r,mem,eq⟩ := List.mem_map.mp required
    change node? left (i+1) = node? right (i+1)
    rw [← eq,leftRows r mem,rightRows r mem]
  · simp [Array.getElem?_eq_none_iff.mpr (by omega : left.size ≤ i),
      Array.getElem?_eq_none_iff.mpr (by omega : right.size ≤ i)]

/-- The allocator's actual four-limb length represents its three-limb contents authorization. -/
theorem length_bits {r : Step F} (valid : r.Valid) :
    Word.toBitVec64 r.node.node.length = BitVec.ofNat 64 (Address.toNat r.length) := by
  rw [Word.toBitVec64, Word.toNat_def, valid.2.2.1]
  simp [Address.toNat,Step.length]

end SP1Clean.WriteAllocation
