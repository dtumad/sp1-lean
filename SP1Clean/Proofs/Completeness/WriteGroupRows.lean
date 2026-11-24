import SP1Clean.Proofs.Operations.WriteGroup
import SP1Clean.Proofs.Completeness.WriteEffectRows

/-! # Constructing and reading grouped WRITE rows

Groups take the original observed octets, the incoming stream position and the actual data
buffer. A single aligned guest word may span two destination blocks. Every positional equality
is stated over ordinary byte indices, including the exact last lane of a partial block.
-/

namespace SP1Clean.WriteEffects
open Semantics

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- The witness columns for a single observed word, even when its selected window is empty. -/
def Group.populate (octets : Octets (ZMod p)) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (first size base : Nat) (bytes : Bytes) : Group (ZMod p) :=
  let position := Address.ofNat (p := p) base
  let index := base/8
  let aligned := fun i => (HintQueue.wordBytes bytes i).map (fun b => (b.toNat : ZMod p))
  {octets, previous := ⟨octets.clock,sink,owner,Address.ofNat (Address.toNat octets.key + first - 1),position⟩
   plan := .ofNat first size (base%8), ignored := if sink = 0 then 1 else 0
   quotients := (AddressDiv8.populate (Address.asWord position)).quotients
   firstBlock := Address.ofNat index, nextBlock := Address.ofNat (index+1), nextPosition := Address.ofNat (base+size)
   leftSize := (min 8 (bytes.length - 8 * index) : Nat), rightSize := (min 8 (bytes.length - 8*(index+1)) : Nat)
   left := aligned index, right := aligned (index+1)}

omit [Fact (2^17 < p)] in
private theorem short_address (n : Nat) (small : n < 2^16) :
    Address.ofNat (p := p) n = #v[(n : ZMod p),0,0] := by
  simp only [Address.ofNat,Nat.mod_eq_of_lt small,Nat.div_eq_of_lt small,Nat.div_eq_of_lt (show n < 2^32 by omega),
    Nat.zero_mod,Nat.cast_zero]

omit [Fact (2^17 < p)] in
private theorem offset_aligned (word lane : Nat) (small : lane < 8) :
    Address.offset (Address.ofNat (8*word)) (lane : ZMod p) = Address.ofNat (8*word + lane) := by
  have low : 8*word%65536+lane = (8*word+lane)%65536 := by omega
  have mid : 8*word/65536 = (8*word+lane)/65536 := by omega
  have hi : 8*word/4294967296 = (8*word+lane)/4294967296 := by omega
  simp only [Address.offset,Address.ofNat,circuit_norm,Nat.reducePow,← Nat.cast_add,low,mid,hi]

private theorem sum_ofNat (a b : Nat) (bound : a+b < 2^48) :
    AddressSum.Spec (p := p) ⟨Address.ofNat a,Address.ofNat b,Address.ofNat (a+b)⟩ := by
  refine ⟨Address.bounded_ofNat _,Address.bounded_ofNat _,Address.bounded_ofNat _,?_⟩
  simp only [Address.toNat_ofNat _ (by omega : a < 2^48),Address.toNat_ofNat _ (by omega : b < 2^48),
    Address.toNat_ofNat _ bound]

/-- Source and output cursor columns implement the natural window bounds, without wrapping
even when the last selected guest address is the last representable RAM address. -/
theorem Group.populate_coordinates (octets : Octets (ZMod p)) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (first size base word : Nat) (bytes : Bytes) (key : octets.key = Address.ofNat (8*word))
    (f : first < 8) (n : first + size ≤ 8) (positive : 0 < 8*word + first)
    (guest : 8*word < 2^48) (out : base+size < 2^48) :
    (Group.populate octets sink owner first size base bytes).HonestCoordinates := by
  have baseNat := Address.toNat_ofNat (p := p) base (by omega)
  have indexNat := Address.toNat_ofNat (p := p) (base/8) (by omega)
  have hp : 2^17 < p := Fact.out
  have firstAddr : Address.offset octets.key (first : ZMod p) = Address.ofNat (8*word+first) := by rw [key,offset_aligned word first f]
  have addOne : 8*word+first-1+1 = 8*word+first := by omega
  have firstSum := sum_ofNat (p := p) (8*word+first-1) 1 (by omega)
  rw [addOne,short_address 1 (by decide)] at firstSum
  have byteSum := sum_ofNat (p := p) base size out
  rw [short_address size (by omega)] at byteSum
  have blockSum := sum_ofNat (p := p) (base/8) 1 (by omega)
  rw [short_address 1 (by decide)] at blockSum
  simp only [Nat.cast_one] at firstSum blockSum
  refine ⟨⟨rfl,Address.bounded_ofNat _,indexNat.trans (congrArg (· / 8) baseNat.symm),?_,?_,byteSum,blockSum⟩,rfl⟩
  · change (↑(base%8) : ZMod p).val = Address.toNat (Address.ofNat base)%8
    rw [baseNat,ZMod.val_natCast_of_lt (by omega)]
  · change AddressSum.Spec ⟨Address.ofNat (Address.toNat octets.key+first-1),#v[1,0,0],Address.offset octets.key (first : ZMod p)⟩
    rw [firstAddr,key,Address.toNat_ofNat _ guest]
    exact firstSum

omit [Fact (2^17 < p)] in
/-- The ordinary little-endian byte recovered from the actual string at its absolute position.
Only the two blocks straddling the beginning of the interval are ever addressed. -/
private theorem block_lane (bytes : Bytes) (base : Nat) (slot : Fin 8) :
    let aligned := fun i => (HintQueue.wordBytes bytes i).map (fun b => (b.toNat : ZMod p))
    (if base%8 + slot.val < 8 then (aligned (base/8))[(base%8+slot.val)%8]
     else (aligned (base/8+1))[(base%8+slot.val)%8]) =
      ((bytes[base+slot.val]?.getD 0).toNat : ZMod p) := by
  dsimp only
  split <;> rename_i cut
  · simp only [HintQueue.wordBytes,Vector.getElem_map,Vector.getElem_ofFn]
    rw [show base/8*8+(base%8+slot.val)%8 = base+slot.val by omega]
  · simp only [HintQueue.wordBytes,Vector.getElem_map,Vector.getElem_ofFn]
    rw [show (base/8+1)*8+(base%8+slot.val)%8 = base+slot.val by have := slot.isLt; omega]

/-- The physical byte test is equivalent, in both directions, to positional equality for each
selected guest lane. Disabled sinks still supply the entire original octets receipt. -/
theorem Group.populate_match_iff (octets : Octets (ZMod p)) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (first size base : Nat) (bytes : Bytes) (f : first < 8) :
    (Group.populate octets sink owner first size base bytes).BytesMatch ↔
      ∀ slot : Fin 8, sink ≠ 0 → slot.val < size →
        octets.bytes[(first+slot.val)%8] = ((bytes[base+slot.val]?.getD 0).toNat : ZMod p) := by
  constructor
  · intro physical slot output used
    have checked := Group.BytesMatch.atLane physical (first := first) (size := size) (offset := base%8)
      rfl f (by omega) slot used (by simp [Group.populate,output])
    exact checked.trans (block_lane bytes base slot)
  · intro actual slot output active
    have used : slot.val < size := by
      by_contra empty
      exact active (by simp [Group.populate,SlicePlan.ofNat,empty])
    have nonzero : sink ≠ 0 := by
      rintro rfl
      exact output (by simp [Group.populate])
    change (SlicePlan.ofNat (p := p) first size (base%8)).guestByte octets.bytes slot =
      (SlicePlan.ofNat first size (base%8)).streamByte _ _ slot
    rw [guestByte_ofNat f,streamByte_ofNat (by omega)]
    exact (actual slot nonzero used).trans (block_lane bytes base slot).symm

private theorem extents_populate (octets : Octets (ZMod p)) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (first size base : Nat) (bytes : Bytes) (n : first+size ≤ 8)
    (endBound : sink ≠ 0 → 0 < size → base+size ≤ bytes.length) :
    (Group.populate octets sink owner first size base bytes).Extents := by
  let r := Group.populate octets sink owner first size base bytes
  have hp : 2^17 < p := Fact.out
  have left : r.leftSize.val = min 8 (bytes.length - 8*(base/8)) := ZMod.val_natCast_of_lt (by omega)
  have right : r.rightSize.val = min 8 (bytes.length - 8*(base/8+1)) := ZMod.val_natCast_of_lt (by omega)
  have a : r.plan.firstExtent.val = min 8 (size+base%8) := ZMod.val_natCast_of_lt (by omega)
  have b : r.plan.secondExtent.val = size+base%8-8 := ZMod.val_natCast_of_lt (by omega)
  change r.Extents
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩
  · intro used
    have nz : sink ≠ 0 := by rintro rfl; simp [r,Group.leftGate,Group.populate] at used
    have pos : 0 < size := by
      by_contra zero
      have h : size=0 := by omega
      simp [r,Group.leftGate,Group.populate,SlicePlan.ofNat,h] at used
    have paid := endBound nz pos
    omega
  · intro used
    have nz : sink ≠ 0 := by rintro rfl; simp [r,Group.rightGate,Group.populate] at used
    have crossed : 8 < size+base%8 := by
      by_contra absent
      simp [r,Group.rightGate,Group.populate,SlicePlan.ofNat,absent] at used
    have paid := endBound nz (by omega)
    omega

/-- Populate all grouped circuit columns from the real word and destination buffer. The
ordinary per-byte statement is sufficient even for unaligned, cross-block and ignored words. -/
theorem Group.populate_valid (octets : Octets (ZMod p)) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (first size base word : Nat) (bytes : Bytes) (key : octets.key = Address.ofNat (8*word))
    (f : first < 8) (n : first+size ≤ 8) (positive : 0 < 8*word+first) (guest : 8*word < 2^48) (out : base+size < 2^48)
    (endBound : sink ≠ 0 → 0 < size → base+size ≤ bytes.length)
    (same : ∀ slot : Fin 8, sink ≠ 0 → slot.val < size →
      octets.bytes[(first+slot.val)%8] = ((bytes[base+slot.val]?.getD 0).toNat : ZMod p)) :
    let r := Group.populate octets sink owner first size base bytes
    r.Valid ∧ r.HonestCoordinates := by
  have coords := populate_coordinates octets sink owner first size base word bytes key f n positive guest out
  have bit (q : Prop) [Decidable q] : IsBool (if q then 1 else 0 : ZMod p) := by by_cases h : q <;> simp [h,IsBool]
  exact ⟨⟨coords.1,(populate_match_iff octets sink owner first size base bytes f).mpr same,rfl,by
    by_cases z : size=0 <;> simp [populate,SlicePlan.ofNat,z,IsBool], bit _,extents_populate octets sink owner first size base bytes n endBound⟩,coords⟩

end SP1Clean.WriteEffects
