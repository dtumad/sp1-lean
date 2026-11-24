import SP1Clean.Proofs.Operations.AddrAddOperation.Address
import SP1Clean.Native.Operations.WordRangeCheck

/-! # Self-contained, nonwrapping addition on three-limb addresses

The operands and result are locally bit-decomposed. The four carry equations use the released
address adder's existing soundness and completeness proof, with no shared Byte lookups. This interface is suitable for packet addresses and chronological positions
whose previous values come from a private channel.
-/

namespace SP1Clean.AddressSum
open Circuit

/-- Two unsigned address operands and their canonical nonwrapping sum. -/
structure Inputs (F : Type) where
  /-- First three-limb address operand. -/
  left : fields 3 F
  /-- Second three-limb address operand. -/
  right : fields 3 F
  /-- Canonical three-limb representation of the sum. -/
  result : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Both operands and the result represent addresses whose natural values add exactly. -/
def Spec (x : Inputs (ZMod p)) : Prop := Address.Bounded x.left ∧ Address.Bounded x.right ∧
  Address.Bounded x.result ∧ Address.toNat x.result = Address.toNat x.left + Address.toNat x.right

/-- Canonical encodings of an exact natural sum satisfy the address adder. -/
theorem spec_ofNat (a b : Nat) (bound : a+b < 2^48) :
    Spec (p := p) ⟨Address.ofNat a,Address.ofNat b,Address.ofNat (a+b)⟩ := by
  refine ⟨Address.bounded_ofNat _,Address.bounded_ofNat _,Address.bounded_ofNat _,?_⟩
  simp only [Address.toNat_ofNat _ (by omega : a < 2^48),Address.toNat_ofNat _ (by omega : b < 2^48),
    Address.toNat_ofNat _ bound]

/-- Range-check the operands and constrain the result with the SP1 address adder. -/
def main (x : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit (Address.asWord x.left)
  assertion WordRangeCheck.circuit (Address.asWord x.right)
  assertion WordRangeCheck.circuit (Address.asWord x.result)
  let inv := Expression.const ((65536 : ZMod p)⁻¹)
  let low <== (x.left[0] + x.right[0] - x.result[0]) * inv
  let middle <== (x.left[1] + x.right[1] - x.result[1] + low) * inv
  let high <== (x.left[2] + x.right[2] - x.result[2] + middle) * inv
  assertBool low
  assertBool middle
  assertBool high
  assertBool (high * inv)

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

omit [Fact (2^17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (a : fields 3 (Expression (ZMod p))) :
    eval env (Address.asWord a) = Address.asWord (eval env a) := by simp only [Address.asWord, circuit_norm]

private theorem of_carries (r : Inputs (ZMod p)) (la : (Address.asWord r.left).isU64) (lb : (Address.asWord r.right).isU64)
    (raw : AddrAddOperation.RawSpec (Address.asWord r.left) (Address.asWord r.right) ⟨r.result⟩) : Spec r := by
  have copy := raw
  obtain ⟨_, _, _, _, lo, mid, hi⟩ := copy
  have low := Address.bounded_of_isU64_asWord la
  have high := Address.bounded_of_isU64_asWord lb
  have result := AddrAddOperation.exact_sum (Address.asWord r.left) (Address.asWord r.right) r.result
    (fun _ => ⟨AddrAddOperation.addrAddSemantics_of_carries la lb raw, lo, mid, hi,
      AddrAddOperation.addrAddFits_of_carries la lb raw⟩)
    (by rw [Address.toNat_asWord, Address.toNat_asWord]; have := Address.toNat_lt low; have := Address.toNat_lt high; omega)
  exact ⟨low, high, result.1, by simpa only [Address.toNat_asWord] using result.2.1⟩

private theorem to_carries (r : Inputs (ZMod p)) (valid : Spec r) :
    (Address.asWord r.left).isU64 ∧ (Address.asWord r.right).isU64 ∧ (Address.asWord r.result).isU64 ∧
      AddrAddOperation.RawSpec (Address.asWord r.left) (Address.asWord r.right) ⟨r.result⟩ := by
  obtain ⟨a,b,c,sum⟩ := valid
  obtain ⟨value,low,middle,high,fit⟩ := (AddrAddOperation.spec_of_sum (Address.asWord r.left) (Address.asWord r.right) r.result c
    (by simpa only [Address.toNat_asWord] using sum)) rfl
  exact ⟨Address.isU64_asWord a,Address.isU64_asWord b,Address.isU64_asWord c,
    AddrAddOperation.carries_of_addrAddSemantics (Address.isU64_asWord a) (Address.isU64_asWord b) fit low middle high value⟩

/-- Bundled assertion for exact addition in the 48-bit address domain. -/
def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  computableWitnesses := by computable_witnesses [Address.asWord]
  Spec := Spec
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, eval_asWord]
    obtain ⟨a,b,c,low,middle,high,lb,mb,hb,top⟩ := h_holds
    have out := Address.bounded_of_isU64_asWord c
    rw [high,middle,low] at top hb
    rw [middle,low] at mb
    rw [low] at lb
    apply of_carries ⟨input_left,input_right,input_result⟩ a b
    exact ⟨lb,mb,hb,by simpa only [IsBool,Address.asWord,zero_add,circuit_norm] using top,out 0,out 1,out 2⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, eval_asWord]
    obtain ⟨a,b,c,lb,mb,hb,top,_,_,_⟩ := to_carries ⟨input_left,input_right,input_result⟩ h_spec
    obtain ⟨low,middle,high⟩ := h_env
    refine ⟨a,b,c,low,middle,high,?_,?_,?_,?_⟩
    · simpa only [IsBool,low,Address.asWord,circuit_norm] using lb
    · simpa only [IsBool,middle,low,Address.asWord,circuit_norm] using mb
    · simpa only [IsBool,high,middle,low,Address.asWord,circuit_norm] using hb
    · simpa only [IsBool,high,middle,low,Address.asWord,zero_add,circuit_norm] using top

/-- The complete bounded adder emits neither native nor shared lookup traffic. -/
theorem interactions (x : Var Inputs (ZMod p)) (n : Nat) : ((main x).operations n).interactions = [] := by
  have outside (ch : RawChannel (ZMod p)) : ch ∉ circuit.channels := by
    simp [FormalCircuitBase.channels, circuit, elaborated, circuit_norm]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i member
  apply outside i.channel
  exact circuit.base.channels_subset x n (List.mem_map_of_mem (f := AbstractInteraction.channel) member)

end SP1Clean.AddressSum
