import SP1Clean.Native.Operations.WriteAllocationPayload
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

end SP1Clean.WriteAllocation.Words
