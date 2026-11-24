import SP1Clean.Native.Operations.WriteAllocationWords
import SP1Clean.Math.WordEquality

/-! # Constructing the padded word walk of a fresh WRITE hint

Every physical queue word is exactly the canonical immutable record for this pointer and byte
string, including the mandatory final word of an empty or aligned buffer. The same columns
supply a private direct block or consume a fixed returned block at all occupied positions.
-/

namespace SP1Clean.WriteAllocation.Words
open Semantics Semantics.HintQueue Soundness.Target WriteEffects

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Occupied bytes in word `i` of the actual newly allocated node. -/
def extent (bytes : Bytes) (i : Nat) : Nat := min 8 (bytes.length - 8 * i)

/-- Construct the actual little-endian payload and contiguous live-lane mask. -/
def Payload.populate (bytes : Bytes) (i : Nat) : Payload (ZMod p) :=
  ⟨(wordBytes bytes i).map fun b => (b.toNat : ZMod p),
    Vector.ofFn fun lane => if lane.val < extent bytes i then 1 else 0⟩

/-- Fill the absolute word index, remaining bytes and immutable data for an authorized pointer. -/
def populate (contents : Contents (ZMod p)) (bytes : Bytes) (i : Nat) (blockReads wordReads : ZMod p) : Row (ZMod p) :=
  ⟨⟨contents,Address.ofNat i,Address.ofNat (bytes.length-8 * i)⟩,
    Address.ofNat (Address.toNat contents.pointer-1),Address.ofNat (i+1),
    Address.ofNat (bytes.length-8*(i+1)),Payload.populate bytes i,blockReads,wordReads⟩

omit [Fact (2^17 < p)] in
private theorem lane_sum (n : Nat) (small : n ≤ 8) (lanes : fields 8 (ZMod p)) :
    (Payload.mk lanes (Vector.ofFn fun i => if i.val < n then 1 else 0)).used = (n : ZMod p) := by
  interval_cases n <;> norm_num [Payload.used]

omit [Fact (2^17 < p)] in
/-- The last flag is set on exactly the required final padded position. -/
theorem populate_last (bytes : Bytes) {i : Nat} (inside : i < wordCount bytes) :
    (Payload.populate (p := p) bytes i).last = if i+1 = wordCount bytes then 1 else 0 := by
  simp only [Payload.populate,Payload.last,Payload.more,Vector.getElem_ofFn]
  unfold extent wordCount at *
  split <;> rename_i flag
  · rw [ite_eq_right (by omega)]
    simp
  · rw [ite_eq_left (by omega)]
    simp

/-- The channel record published by any constructed fresh-word row is precisely the queue
record used by persistent-store lookup and all future reads. -/
theorem populate_word (c : Contents (ZMod p)) (bytes : Bytes) (i : Nat) (br wr : ZMod p)
    (pointer : Address.Bounded c.pointer) (inside : i < wordCount bytes) :
    (populate c bytes i br wr).word = WordRecord.encode (Address.toNat c.pointer) bytes i := by
  have packed : Word.ofBytes ((wordBytes bytes i).map (fun b => (b.toNat : ZMod p))) = bitVecToWord (wordValue bytes i) :=
    Word.eq_of_toBitVec64_eq (Word.ofBytes_isU64 _) (isU64_bitVecToWord _) ((Word.toBitVec64_ofBytes _).trans (toBitVec64_bitVecToWord _).symm)
  simp only [Row.word,populate,WordRecord.encode,Address.ofNat_toNat pointer,populate_last bytes inside]
  exact congrArg (fun w => WordRecord.mk c.pointer (Address.ofNat i) w _) packed


omit [Fact (2^17 < p)] in
/-- Number of occupied lanes encoded in the row, including zero in a final padding word. -/
theorem populate_used (bytes : Bytes) (i : Nat) :
    (Payload.populate (p := p) bytes i).used = (extent bytes i : ZMod p) :=
  lane_sum _ (Nat.min_le_left ..) _

/-- Every byte and prefix bit is derived from the actual buffer. -/
theorem populate_payload_valid (bytes : Bytes) (i : Nat) : (Payload.populate (p := p) bytes i).Valid := by
  intro j
  have hp : 2^17 < p := Fact.out
  have bounded := (wordBytes bytes i)[j].isLt
  have small : (wordBytes bytes i)[j].toNat < 256 := bounded
  refine ⟨?_,?_,?_,?_⟩
  · change (((wordBytes bytes i).map (fun b => (b.toNat : ZMod p)))[j.val]).val < 256
    rw [Vector.getElem_map,ZMod.val_natCast_of_lt (by omega : (wordBytes bytes i)[j.val].toNat < p)]
    exact small
  · by_cases live : j.val < extent bytes i <;> simp [Payload.populate,live,IsBool]
  · intro live
    by_cases first : j.val = 0
    · simp [Payload.previous,first]
    · have used : j.val < extent bytes i := by
        by_contra empty
        simp [Payload.populate,empty] at live
      have prior : j.val-1 < extent bytes i := by omega
      simp [Payload.previous,first,Payload.populate,prior]
  · intro absent
    have outside : extent bytes i ≤ j.val := by
      by_contra! live
      simp [Payload.populate,live] at absent
    have behind : bytes.length ≤ i * 8 + j.val := by
      have := j.isLt
      unfold extent at outside
      omega
    simp [Payload.populate,wordBytes,List.getElem?_eq_none_iff.mpr behind]

omit [Fact (2^17 < p)] in
private theorem small_address (n : Nat) (small : n < 2^16) :
    Address.ofNat (p := p) n = #v[(n : ZMod p),0,0] := by
  simp only [Address.ofNat,Nat.mod_eq_of_lt small,Nat.div_eq_of_lt small,Nat.div_eq_of_lt (show n < 2^32 by omega),
    Nat.zero_mod,Nat.cast_zero]

/-- Honest construction of every active row, with the complete node's actual length.
Neither the read multiplicities nor the choice of direct or hook data restrict its contents. -/
theorem populate_valid (c : Contents (ZMod p)) (bytes : Bytes) (i : Nat) (br wr : ZMod p)
    (mode : IsBool c.direct) (bounded : Address.Bounded c.pointer) (positive : 0 < Address.toNat c.pointer)
    (length : bytes.length < 2^48) (inside : i < wordCount bytes) :
    (populate c bytes i br wr).Valid := by
  have index : i < bytes.length / 8 + 1 := inside
  have w := Address.toNat_lt bounded
  have pred : Address.toNat c.pointer-1+1 = Address.toNat c.pointer := by omega
  have pointerSum := AddressSum.spec_ofNat (p := p) (Address.toNat c.pointer-1) 1 (by omega)
  rw [pred,Address.ofNat_toNat bounded,small_address 1 (by decide),Nat.cast_one] at pointerSum
  have indexSum := AddressSum.spec_ofNat (p := p) i 1 (by omega)
  rw [small_address 1 (by decide),Nat.cast_one] at indexSum
  have fit : extent bytes i ≤ 8 := Nat.min_le_left ..
  have sum : bytes.length-8*(i+1) + extent bytes i = bytes.length-8 * i := by unfold extent; omega
  have count := AddressSum.spec_ofNat (p := p) (bytes.length-8*(i+1)) (extent bytes i) (by omega)
  rw [sum,small_address (extent bytes i) (by omega)] at count
  refine ⟨mode,populate_payload_valid bytes i,pointerSum,indexSum,?_,?_⟩
  · simpa only [populate,populate_used] using count
  · change (Payload.populate (p := p) bytes i).last = 1 → Address.ofNat (bytes.length-8*(i+1)) = #v[0,0,0]
    rw [populate_last bytes inside]
    split
    · rename_i last
      have z : bytes.length-8*(i+1) = 0 := by change i+1 = bytes.length/8+1 at last; omega
      rw [z,small_address 0 (by decide),Nat.cast_zero]
      exact fun _ => rfl
    · simp

omit [Fact (2^17 < p)] in
/-- Hook rows consume the exact occupied block of the supplied reply, at both original ordinals. -/
theorem populate_returned (c : Contents (ZMod p)) (bytes : Bytes) (i reply index : Nat) (br wr : ZMod p)
    (owner : c.reply = Address.ofNat reply) (atHint : c.index = Address.ofNat index) :
    (populate c bytes i br wr).returned = encodeBlock (.returned reply index) bytes i := by
  simp only [Row.returned,populate,owner,atHint,populate_used]
  rfl

omit [Fact (2^17 < p)] in
/-- A private direct block is keyed by the same fresh node and shares all eight persistent bytes. -/
theorem populate_direct (c : Contents (ZMod p)) (bytes : Bytes) (i : Nat) (br wr : ZMod p) :
    (populate c bytes i br wr).direct =
      ⟨14,c.pointer,0,Address.ofNat i,extent bytes i,(wordBytes bytes i).map (fun b => (b.toNat : ZMod p))⟩ := by
  simp only [Row.direct,populate,populate_used]
  rfl


omit [Fact (2^17 < p)] in
/-- The authorization reaches the first word for all lengths, including zero. -/
theorem populate_start (c : Contents (ZMod p)) (bytes : Bytes) (br wr : ZMod p)
    (length : c.length = Address.ofNat bytes.length) : (populate c bytes 0 br wr).prior = start c := by
  simp [populate,start,length,Address.ofNat_zero]

omit [Fact (2^17 < p)] in
/-- Successive physical rows agree on the whole cursor, regardless of their read multiplicities. -/
theorem populate_next (c : Contents (ZMod p)) (bytes : Bytes) (i : Nat) (br wr br' wr' : ZMod p) :
    (populate c bytes i br wr).next = (populate c bytes (i+1) br' wr').prior := rfl

/-- The word rows the compiler offers to the demand scheduler, in immutable pointer order.
Each read multiplicity is owned by that physical word position. -/
def walk (c : Contents (ZMod p)) (bytes : Bytes) (br wr : Nat → ZMod p) : List (Row (ZMod p)) :=
  List.ofFn fun i : Fin (wordCount bytes) => populate c bytes i.val (br i.val) (wr i.val)

omit [Fact (2^17 < p)] in
/-- The allocation contributes its full padded height before Clean demand padding. -/
theorem walk_length (c : Contents (ZMod p)) (bytes : Bytes) (br wr : Nat → ZMod p) :
    (walk c bytes br wr).length = wordCount bytes := by simp [walk]

/-- Each output at this pointer agrees with the independently defined complete immutable-word inventory. -/
theorem walk_words (c : Contents (ZMod p)) (bytes : Bytes) (br wr : Nat → ZMod p)
    (pointer : Address.Bounded c.pointer) (length : bytes.length < 2^48) :
    (walk c bytes br wr).map Row.word = nodeWordRows (Address.toNat c.pointer) bytes := by
  have size : wordCount bytes ≤ 2^48 := by unfold wordCount; omega
  simp only [walk,nodeWordRows,Nat.min_eq_left size,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact populate_word c bytes i.val _ _ pointer i.isLt

omit [Fact (2^17 < p)] in
/-- A live hook read appears in the checked public provider table at the same reply and hint ordinals. -/
theorem populate_hook_available (streams : WriteStreams) (checked : inventoryOK streams = true)
    (c : Contents (ZMod p)) (bytes : Bytes) (i reply index : Nat) (br wr : ZMod p)
    (owner : c.reply = Address.ofNat reply) (atHint : c.index = Address.ofNat index)
    (source : (StreamKey.returned reply index).contents streams = some bytes)
    (occupied : 8 * i < bytes.length) :
    (blockTable streams).Spec (populate c bytes i br wr).returned := by
  rw [populate_returned c bytes i reply index br wr owner atHint]
  exact block_available checked source occupied

end SP1Clean.WriteAllocation.Words
