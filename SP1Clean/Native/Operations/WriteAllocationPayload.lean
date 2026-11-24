import SP1Clean.FormalModel.Contracts.WriteAllocationWords
import SP1Clean.Native.Operations.WordRangeCheck
import Clean.Gadgets.Boolean

/-! # Exact occupied prefix, zero padding and byte validity for a fresh hint word

Every lane is locally range checked. A live lane requires its predecessor to be live, and
every unused lane must be zero. The physical word and both block encodings use the same bytes.
-/

namespace SP1Clean.WriteAllocation.Words
open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

omit [Fact p.Prime] in
private theorem width : 2^8 < p := by have h : 2^17 < p := Fact.out; omega

/-- Each lane contains a genuine byte, and occupancy is a prefix with zero padding. -/
def Payload.Valid (r : Payload (ZMod p)) : Prop :=
  ∀ i : Fin 8, r.bytes[i].val < 256 ∧ IsBool r.mask[i] ∧
    (r.mask[i] = 1 → r.previous i = 1) ∧ (r.mask[i] = 0 → r.bytes[i] = 0)

/-- Derive the eight bounded bytes and require the occupied lanes to be contiguous. -/
def payloadMain (r : Var Payload (ZMod p)) : Circuit (ZMod p) Unit := do
  forEach (Vector.ofFn fun i : Fin 8 => i) fun i => do
    assertion (Gadgets.ToBits.rangeCheck 8 width) r.bytes[i]
    assertBool r.mask[i]
    assertZero (r.mask[i]*(1-r.previous i))
    assertZero ((1-r.mask[i])*r.bytes[i])

/-- The range-check and prefix constraints of all lanes. -/
instance payloadElaborated : ElaboratedCircuit (ZMod p) Payload unit payloadMain := by elaborate_circuit

omit [Fact (2^17 < p)] in
private theorem previous_eval (r : Var Payload (ZMod p)) (env : Environment (ZMod p)) (i : Fin 8) :
    (r.previous i).eval env = (eval env r).previous i := by
  unfold Payload.previous
  split <;> simp only [circuit_norm]

omit [Fact (2^17 < p)] in
private theorem lane_iff (flag prev byte : ZMod p) (bit : IsBool flag) :
    (flag*(1-prev)=0 ∧ (1-flag)*byte=0) ↔ ((flag=1 → prev=1) ∧ (flag=0 → byte=0)) := by
  constructor
  · rintro ⟨prior,pad⟩
    constructor
    · intro one
      rw [one,one_mul,sub_eq_zero] at prior
      exact prior.symm
    · intro zero
      simpa only [zero,sub_zero,one_mul] using pad
  · rintro ⟨prior,pad⟩
    rcases bit with zero|one
    · simp [zero,pad zero]
    · simp [one,prior one]

/-- Local formal assertion shared by persistent words and fresh direct or returned blocks. -/
def payloadCircuit : FormalAssertion (ZMod p) Payload where
  main := payloadMain
  elaborated := payloadElaborated
  computableWitnesses := by computable_witnesses [Payload.previous]
  Spec := Payload.Valid
  soundness := by
    circuit_proof_start [payloadMain,Gadgets.ToBits.rangeCheck,previous_eval]
    intro i
    obtain ⟨byte,bit,prev,pad⟩ := h_holds i
    exact ⟨byte,bit,(lane_iff _ _ _ bit).mp ⟨prev,pad⟩⟩
  completeness := by
    circuit_proof_start [payloadMain,Gadgets.ToBits.rangeCheck,previous_eval]
    intro i
    obtain ⟨byte,bit,prev,pad⟩ := h_spec i
    exact ⟨byte,bit,(lane_iff _ _ _ bit).mpr ⟨prev,pad⟩⟩

/-- A valid field-valued payload packs to a genuine four-limb persistent queue word. -/
theorem Payload.Valid.packed {r : Payload (ZMod p)} (valid : r.Valid) : (Word.ofBytes r.bytes).isU64 := by
  let b := r.bytes.map fun x => BitVec.ofNat 8 x.val
  have same : b.map (fun x => (x.toNat : ZMod p)) = r.bytes := by
    apply Vector.ext
    intro i bound
    have small := (valid ⟨i,bound⟩).1
    change r.bytes[i].val < 2^8 at small
    simp only [b,Vector.getElem_map,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,ZMod.natCast_zmod_val]
  rw [← same]
  exact Word.ofBytes_isU64 b

omit [Fact (2^17 < p)] in
/-- Summing a prefix of unit lane activities returns the actual occupied count. -/
theorem Payload.used_prefix (n : Nat) (small : n ≤ 8) (lanes : fields 8 (ZMod p)) :
    (Payload.mk lanes (Vector.ofFn fun i => if i.val < n then 1 else 0)).used = (n : ZMod p) := by
  interval_cases n <;> norm_num [Payload.used]

omit [Fact (2^17 < p)] in
/-- Arbitrary checked bytes have one uniquely positioned contiguous occupancy prefix.
The terminal row has strictly fewer than eight occupied lanes. -/
theorem Payload.Valid.prefix {r : Payload (ZMod p)} (valid : r.Valid) :
    ∃ n ≤ 8, (∀ i : Fin 8, r.mask[i] = if i.val < n then 1 else 0) ∧
      r.used = (n : ZMod p) ∧ (r.more = 1 ↔ n = 8) := by
  classical
  let stop := fun n : Nat => ∀ h : n < 8, r.mask[n] = 0
  have existsEnd : ∃ n, stop n := ⟨8,fun h => (Nat.lt_irrefl _ h).elim⟩
  let n := Nat.find existsEnd
  have bound : n ≤ 8 := Nat.find_min' existsEnd (fun h => (Nat.lt_irrefl _ h).elim : stop 8)
  have tailZero : ∀ k, n ≤ k → ∀ small : k < 8, r.mask[k] = 0 := by
    intro k after
    induction k, after using Nat.le_induction with
    | base => exact Nat.find_spec existsEnd
    | succ k after ih =>
      intro small
      obtain dead|live := (valid ⟨k+1,small⟩).2.1
      · exact dead
      · have prev := (valid ⟨k+1,small⟩).2.2.1 live
        have z := ih (by omega)
        simp [Payload.previous,z] at prev
  have mask (i : Fin 8) : r.mask[i] = if i.val < n then 1 else 0 := by
    split
    · rename_i before
      obtain dead|live := (valid i).2.1
      · exact False.elim (Nat.find_min existsEnd before (fun _ => dead))
      · exact live
    · exact tailZero i.val (by omega) i.isLt
  have shape : r.mask = Vector.ofFn (fun i : Fin 8 => if i.val < n then 1 else 0) := by
    ext i h
    rw [Vector.getElem_ofFn]
    exact mask ⟨i,h⟩
  refine ⟨n,bound,mask,?_,?_⟩
  · calc
      r.used = (Payload.mk r.bytes (Vector.ofFn (fun i : Fin 8 => if i.val < n then 1 else 0))).used := by
        simp only [Payload.used,shape]
      _ = _ := Payload.used_prefix n bound _
  · change r.mask[7] = 1 ↔ n = 8
    have lastLane : r.mask[7] = if 7 < n then 1 else 0 := mask ⟨7,by decide⟩
    rw [lastLane]
    split <;> rename_i last
    · simp [show n = 8 by omega]
    · simp [show n ≠ 8 by omega]

end SP1Clean.WriteAllocation.Words
