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

end SP1Clean.WriteAllocation.Words
