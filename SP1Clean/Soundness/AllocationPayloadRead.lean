import SP1Clean.Soundness.AllocationWordWalk

/-! # Recovering a stored buffer from its complete set of physical allocation words -/

namespace SP1Clean.WriteAllocation
open Semantics Semantics.HintQueue Soundness
private abbrev F := ZMod SP1Prime

private theorem low_length (w : Word F) (hi : w[3] = 0) :
    Word.toNat w = Address.toNat (#v[w[0],w[1],w[2]] : fields 3 F) := by
  rw [Word.toNat_def,hi]
  simp [Address.toNat]

/-- Physical byte lanes at a named word index determine its exact natural padded value. -/
theorem Words.Row.value_of_lanes {r : Words.Row F} (v : r.Valid) (bytes : Bytes) (i : Nat)
    (lanes : ∀ j : Fin 8, r.payload.bytes[j].val = (bytes[i*8+j.val]?.getD 0).toNat) :
    Word.toBitVec64 r.word.value = wordValue bytes i := by
  change Word.toBitVec64 (Word.ofBytes r.payload.bytes) = Word.bytesValue _
  rw [Word.toBitVec64_ofByteFields _ (fun j => (v.2.1 j).1)]
  apply congrArg Word.bytesValue
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map,wordBytes,Vector.getElem_ofFn]
  have atLane : r.payload.bytes[j].val = (bytes[i*8+j]?.getD 0).toNat := lanes ⟨j,hj⟩
  rw [atLane]
  exact BitVec.ofNat_toNat 8 _

/-- The explicit last physical word fixes the stored natural length at its allocating node. -/
theorem stored_length {store : Store} {n : Step F} (nv : n.Valid) {last : Words.Row F}
    (binding : n.node.node.Binds store) (lv : last.Valid) (word : last.word.Binds store)
    (owner : last.word.pointer = n.node.node.pointer) (ends : last.word.isLast = 1)
    {node : HintQueue.Node} (found : node? store (Address.toNat n.node.node.pointer) = some node) :
    node.bytes.length = Address.toNat n.length :=
  (binding.length_eq_of_last nv.2.1.2.2.2.2.1 last.word word lv.word_valid owner ends found).symm.trans
    (low_length n.node.node.length nv.2.2.1)

/-- The exact byte extracted from an authenticated physical word of the persistent store. -/
theorem Words.Row.stored_lane {r : Words.Row F} (v : r.Valid) {store : Store} (bound : r.word.Binds store)
    {node : HintQueue.Node} (found : node? store (Address.toNat r.word.pointer) = some node) (j : Fin 8) :
    BitVec.ofNat 8 r.payload.bytes[j].val = (node.bytes[Address.toNat r.word.index * 8 + j.val]?.getD 0) := by
  have equal := (bound.value found).2
  change Word.toBitVec64 (Word.ofBytes r.payload.bytes) = wordValue node.bytes (Address.toNat r.word.index) at equal
  rw [Word.toBitVec64_ofByteFields _ (fun i => (v.2.1 i).1)] at equal
  have lane := congrArg (fun w : BitVec 64 => w.extractLsb' (8 * j.val) 8) equal
  simpa only [wordValue,Word.bytesValue_extract,wordBytes,Fin.getElem_fin,Vector.getElem_map,Vector.getElem_ofFn] using lane

/-- A complete physical buffer walk authenticates the full natural byte list at its fresh
pointer. The final word discharges the length bound even for an unused or empty buffer. -/
theorem read_payload (store : Store) (n : Step F) (nv : n.Valid) {rows : List (Words.Row F)}
    (walk : Walk.IsWalk Words.wordEdge (some (Words.start n.contents)) none rows)
    (binding : n.node.node.Binds store) (valid : ∀ r ∈ rows,r.Valid) (words : ∀ r ∈ rows,r.word.Binds store)
    (claimed : Bytes) (count : claimed.length = Address.toNat n.length)
    (lanes : ∀ i : Fin rows.length, let r := rows[i.val]
      ∀ j : Fin 8, r.payload.bytes[j].val = (claimed[i.val*8+j.val]?.getD 0).toNat) :
    node? store (Address.toNat n.node.node.pointer) = some ⟨claimed,Address.toNat n.node.node.tail⟩ := by
  have metadata := binding
  obtain ⟨node,atNode,tail,_⟩ := metadata
  obtain ⟨positions,last,member,pointer,number,endWord⟩ := Words.walk_inventory n.contents rows walk valid
  have lastHere : last.word.pointer = n.node.node.pointer := pointer
  have len := count.trans (stored_length nv binding (valid _ member) (words _ member) lastHere endWord atNode).symm
  have atLast : node? store (Address.toNat last.word.pointer) = some node := by rwa [lastHere]
  have size := number.symm.trans (((words _ member).isLast_iff atLast).mp endWord)
  have equal : claimed = node.bytes := by
    apply bytes_eq_of_word_records (p := SP1Prime) atNode claimed len
    intro i h
    have inside : i < rows.length := by simpa only [size,wordCount,← len] using h
    let r := rows[i]
    obtain ⟨pointer,idx⟩ := positions ⟨i,inside⟩
    exact ⟨r.word,words _ (List.getElem_mem inside),congrArg Address.toNat pointer,idx,
      Words.Row.value_of_lanes (valid _ (List.getElem_mem inside)) claimed i (lanes ⟨i,inside⟩)⟩
  rw [atNode,equal,tail]

end SP1Clean.WriteAllocation
