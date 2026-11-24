import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Math.Address

/-! # The byte just before a native WRITE buffer

The represented address plus one may equal the exclusive upper RAM endpoint, including when
an empty packet starts at exactly 2^48. The comparison uses a full four-limb destination.
-/

namespace SP1Clean.WriteStart
open Circuit

/-- Predecessor address and complete guest buffer address at WRITE entry. -/
structure Inputs (F : Type) where
  /-- Three-limb address immediately before the start of the guest buffer. -/
  previous : fields 3 F
  /-- Full four-limb guest buffer address supplied by WRITE. -/
  address : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- The full guest address is the natural-number successor of the bounded predecessor. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  Address.Bounded r.previous ∧ r.address.isU64 ∧ r.address.toNat = Address.toNat r.previous + 1

/-- Range-check the predecessor and enforce the full-width increment to the guest address. -/
def main (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit (Address.asWord r.previous)
  assertion AddOperation.circuit ⟨Address.asWord r.previous, #v[1,0,0,0], ⟨r.address⟩, 1⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

omit [Fact (2^17 < p)] in
private theorem unitWord : Word.isU64 (#v[1,0,0,0] : Word (ZMod p)) ∧
    Word.toNat (#v[1,0,0,0] : Word (ZMod p)) = 1 := by
  constructor
  · apply Word.isU64_of_cases <;> simp only [circuit_norm, ZMod.val_one, ZMod.val_zero] <;> omega
  · simp [Word.toNat_def, ZMod.val_one]

omit [Fact (2^17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (a : fields 3 (Expression (ZMod p))) :
    eval env (Address.asWord a) = Address.asWord (eval env a) := by simp only [Address.asWord, circuit_norm]

omit [Fact (2^17 < p)] in
private theorem sum_of_words (a b c : Word (ZMod p)) (ha : a.isU64) (hb : b.isU64) (hc : c.isU64)
    (bounded : a.toNat + b.toNat < 2^64) (sum : c.toBitVec64 = a.toBitVec64 + b.toBitVec64) :
    c.toNat = a.toNat + b.toNat := by
  have eq := congrArg BitVec.toNat sum
  change c.toBitVec64.toNat = (a.toBitVec64 + b.toBitVec64).toNat at eq
  rw [Word.toBitVec64_toNat hc, BitVec.toNat_add, Word.toBitVec64_toNat ha, Word.toBitVec64_toNat hb, Nat.mod_eq_of_lt bounded] at eq
  exact eq

omit [Fact (2^17 < p)] in
private theorem start_sound (previous : fields 3 (ZMod p)) (address : Word (ZMod p))
    (bound : (Address.asWord previous).isU64)
    (sum : AddOperation.Assumptions ⟨Address.asWord previous, #v[1,0,0,0], ⟨address⟩, 1⟩ →
      AddOperation.Spec ⟨Address.asWord previous, #v[1,0,0,0], ⟨address⟩, 1⟩) :
    Spec ⟨previous, address⟩ := by
  obtain ⟨dest, eq⟩ := (sum ⟨fun _ => ⟨bound, (unitWord (p := p)).1⟩, Or.inr rfl⟩) rfl
  have small := Address.bounded_of_isU64_asWord bound
  have actual := sum_of_words (Address.asWord previous) #v[1,0,0,0] address bound (unitWord (p := p)).1 dest
    (by rw [Address.toNat_asWord, (unitWord (p := p)).2]; have := Address.toNat_lt small; omega) eq
  rw [Address.toNat_asWord, (unitWord (p := p)).2] at actual
  exact ⟨small, dest, actual⟩

omit [Fact (2^17 < p)] in
private theorem start_checks {previous : fields 3 (ZMod p)} {address : Word (ZMod p)} (valid : Spec ⟨previous,address⟩) :
    (Address.asWord previous).isU64 ∧ AddOperation.Assumptions ⟨Address.asWord previous, #v[1,0,0,0], ⟨address⟩, 1⟩ ∧
    AddOperation.Spec ⟨Address.asWord previous, #v[1,0,0,0], ⟨address⟩, 1⟩ := by
  obtain ⟨bound, dest, eq⟩ := valid
  have small := Address.isU64_asWord bound
  refine ⟨small, ⟨fun _ => ⟨small, (unitWord (p := p)).1⟩, Or.inr rfl⟩, fun _ => ⟨dest, ?_⟩⟩
  apply BitVec.eq_of_toNat_eq
  change address.toBitVec64.toNat = ((Address.asWord previous).toBitVec64 + Word.toBitVec64 (#v[1,0,0,0] : Word (ZMod p))).toNat
  rw [BitVec.toNat_add, Word.toBitVec64_toNat dest, Word.toBitVec64_toNat small,
    Word.toBitVec64_toNat (unitWord (p := p)).1, (unitWord (p := p)).2, Address.toNat_asWord,
    Nat.mod_eq_of_lt (by have := Address.toNat_lt bound; omega), eq]

/-- Formal assertion for locating the byte immediately before a guest buffer. -/
def circuit : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  computableWitnesses := by computable_witnesses [Address.asWord]
  Spec
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, AddOperation.circuit, eval_asWord]
    exact start_sound _ _ h_holds.1 h_holds.2
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, AddOperation.circuit, eval_asWord]
    exact start_checks h_spec

end SP1Clean.WriteStart
