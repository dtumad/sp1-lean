import SP1Clean.Proofs.Operations.HintRecordPublications

/-! # Recovering a byte buffer from its physical padded immutable words

A word walk with the authenticated positions determines its underlying bytes. The final
partial or empty padded word is checked against the same decoded byte list as every full word.
-/

namespace SP1Clean.WriteAllocation.Words
open Circuit Semantics Semantics.HintQueue Soundness.Target
private abbrev F := ZMod SP1Prime

private def lanes (r : Row F) := r.payload.bytes.map (fun byte => BitVec.ofNat 8 byte.val)

/-- Read full, little-endian physical words and truncate to the node's true unpadded length. -/
def decodedBytes (c : Contents F) (rows : List (Row F)) : Bytes :=
  (rows.flatMap fun r => (lanes r).toList).take (Address.toNat c.length)

private theorem byteLength (rows : List (Row F)) :
    (rows.flatMap (fun r => (lanes r).toList)).length = 8 * rows.length := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.flatMap_cons,List.length_append,Vector.length_toList,ih,List.length_cons]; omega

private theorem byteAt (rows : List (Row F)) (i : Fin rows.length) (j : Fin 8) :
    (rows.flatMap fun r => (lanes r).toList)[i.val*8+j.val]? = some (lanes rows[i.val])[j] := by
  induction rows with
  | nil => exact Fin.elim0 i
  | cons r rest ih =>
    obtain ⟨i,hi⟩ := i
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.getElem_cons_zero,List.flatMap_cons]
      rw [List.getElem?_append_left (by simpa only [Vector.length_toList] using j.isLt)]
      exact List.getElem?_eq_getElem _
    | succ i =>
      simp only [List.getElem_cons_succ,List.flatMap_cons]
      rw [List.getElem?_append_right (by simp only [Vector.length_toList]; omega)]
      simpa only [Vector.length_toList,show (i+1)*8+j.val-8 = i*8+j.val by omega] using ih ⟨i,by simpa using hi⟩

private theorem absent_lane {i j len : Nat} (unused : ¬i*8+j < len) : ¬j < min 8 (len - (8 * i)) := by omega

/-- The physical positions and remaining counts of a word walk suffice to identify all
its exact canonical records, including the mandatory empty word at an aligned end. -/
theorem decode_records (c : Contents F) (rows : List (Row F))
    (count : rows.length = Address.toNat c.length / 8 + 1)
    (atWord : ∀ i : Fin rows.length, let r := rows[i.val]
      r.Valid ∧ r.prior.contents = c ∧ Address.toNat r.prior.index = i.val ∧
        Address.toNat r.prior.remaining = Address.toNat c.length - (8 * i.val)) :
    (decodedBytes c rows).length = Address.toNat c.length ∧
      ∀ r ∈ rows, r.word ∈ nodeWordRows (p := SP1Prime) (Address.toNat c.pointer) (decodedBytes c rows) := by
  have size : (decodedBytes c rows).length = Address.toNat c.length := by
    simp only [decodedBytes,List.length_take,byteLength,count]
    omega
  refine ⟨size,?_⟩
  intro r member
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp member
  obtain ⟨v,owner,idx,remaining⟩ := atWord ⟨i,hi⟩
  rw [same] at v owner idx remaining
  change Address.toNat r.prior.index = i at idx
  change Address.toNat r.prior.remaining = Address.toNat c.length - (8 * i) at remaining
  have inside : i < wordCount (decodedBytes c rows) := by rwa [wordCount,size,← count]
  have indexSmall : Address.Bounded r.prior.index := v.word_valid.2.2.1
  have indexBound := Address.toNat_lt indexSmall
  have ptrBound : Address.Bounded c.pointer := owner ▸ v.word_valid.1
  have laneMatch : wordBytes (decodedBytes c rows) i = lanes r := by
    apply Vector.ext
    intro j hj
    simp only [wordBytes,Vector.getElem_ofFn]
    by_cases live : i*8+j < Address.toNat c.length
    · have atByte := byteAt rows ⟨i,hi⟩ ⟨j,hj⟩
      rw [same] at atByte
      simp only [decodedBytes,List.getElem?_take,live,↓reduceIte,atByte,Option.getD_some]
      rfl
    · rw [List.getElem?_eq_none (by rw [size]; omega)]
      have outside : ¬j < min 8 (Address.toNat r.prior.remaining) := by rw [remaining]; exact absent_lane live
      have mask := v.bounds.2.2.2 ⟨j,hj⟩
      rw [ite_eq_right outside] at mask
      have zero := (v.2.1 ⟨j,hj⟩).2.2.2 mask
      simp only [lanes,Vector.getElem_map]
      rw [show r.payload.bytes[j] = 0 from zero]
      rfl
  have word : r.word.value = bitVecToWord (wordValue (decodedBytes c rows) i) := by
    apply Word.eq_of_toBitVec64_eq v.word_valid.2.2.2.1 (isU64_bitVecToWord _)
    rw [toBitVec64_bitVecToWord,wordValue,laneMatch]
    exact Word.toBitVec64_ofByteFields _ (fun j => (v.2.1 j).1)
  have last : r.payload.last = if i+1 = wordCount (decodedBytes c rows) then 1 else 0 := by
    rw [wordCount,size]
    have can := v.bounds.2.2.1
    rw [remaining] at can
    rcases (v.2.1 (7 : Fin 8)).2.1 with done | more
    · change r.payload.more = 0 at done
      have stopped : r.payload.more ≠ 1 := by rw [done]; decide
      have limited := mt can.mpr stopped
      rw [ite_eq_left (by omega),Payload.last,done,sub_zero]
    · change r.payload.more = 1 at more
      have enough := can.mp more
      rw [ite_eq_right (by omega),Payload.last,more,sub_self]
  have key : r.prior.index = Address.ofNat i := by rw [← idx,Address.ofNat_toNat indexSmall]
  have record : r.word = WordRecord.encode (Address.toNat c.pointer) (decodedBytes c rows) i := by
    change WordRecord.mk r.prior.contents.pointer r.prior.index r.word.value r.payload.last = _
    rw [WordRecord.encode,owner,Address.ofNat_toNat ptrBound,key,word,last]
  rw [record]
  exact nodeWordRows_complete _ _ _ inside (idx ▸ indexBound)

end SP1Clean.WriteAllocation.Words
