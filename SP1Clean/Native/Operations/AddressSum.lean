import SP1Clean.Proofs.Operations.AddrAddOperation.Address
import SP1Clean.Native.Operations.WordRangeCheck

/-! # Self-contained, nonwrapping addition on three-limb addresses

Both input operands are locally range-checked, and the released address adder checks the result
and its final carry. This interface is suitable for packet addresses and chronological positions
whose previous values come from a private channel.
-/

namespace SP1Clean.AddressSum
open Circuit

structure Inputs (F : Type) where
  left : fields 3 F
  right : fields 3 F
  result : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

def Spec (x : Inputs (ZMod p)) : Prop := Address.Bounded x.left ∧ Address.Bounded x.right ∧
  Address.Bounded x.result ∧ Address.toNat x.result = Address.toNat x.left + Address.toNat x.right

def main (x : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit (Address.asWord x.left)
  assertion WordRangeCheck.circuit (Address.asWord x.right)
  assertion AddrAddOperation.circuit ⟨Address.asWord x.left, Address.asWord x.right, ⟨x.result⟩, 1⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

omit [Fact (2^17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (a : fields 3 (Expression (ZMod p))) :
    eval env (Address.asWord a) = Address.asWord (eval env a) := by simp only [Address.asWord, circuit_norm]

def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  computableWitnesses := by computable_witnesses [Address.asWord]
  Spec := Spec
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions,
      AddrAddOperation.circuit, eval_asWord, Spec]
    obtain ⟨a, b, ran⟩ := h_holds
    have la := Address.bounded_of_isU64_asWord a
    have lb := Address.bounded_of_isU64_asWord b
    obtain ⟨ls, sum, _⟩ := AddrAddOperation.exact_sum _ _ _ (ran ⟨a, b, Or.inr rfl⟩)
      (by rw [Address.toNat_asWord, Address.toNat_asWord]; have := Address.toNat_lt la; have := Address.toNat_lt lb; omega)
    exact ⟨la, lb, ls, by simpa only [Address.toNat_asWord] using sum⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions,
      AddrAddOperation.circuit, eval_asWord, Spec]
    obtain ⟨la, lb, ls, sum⟩ := h_spec
    refine ⟨Address.isU64_asWord la, Address.isU64_asWord lb, ⟨Address.isU64_asWord la, Address.isU64_asWord lb, Or.inr rfl⟩, ?_⟩
    exact AddrAddOperation.spec_of_sum _ _ _ ls (by simpa only [Address.toNat_asWord] using sum)

end SP1Clean.AddressSum
