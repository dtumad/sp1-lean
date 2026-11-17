import SP1Clean.Native.Chips.MulChip.Defs
import SP1Clean.Proofs.CircuitProofStart

/-! # Structural facts for the MUL chip

The subcircuit-list position of MUL's retained R-type reader, kept out of the semantic proof so
timestamp consumers do not depend on MUL's expensive arithmetic completeness theorem. -/

namespace SP1Clean.MulChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The retained R-type reader occurs immediately after MUL's 49-cell witness prefix.  This folded
membership lemma prevents timestamp proofs from normalizing every multiplication assertion. -/
theorem rTypeReader_mem (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ⟨offset + 49,
      Readers.RTypeReader.circuit.toSubcircuit (offset + 49) (rTypeReaderInput input offset)⟩ ∈
      ((main input).operations offset).subcircuits := by
  simp only [main, rTypeReaderInput, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, Witnessable.witness, witnessIR,
    subcircuitWithAssertion, assertion, assertZero, Operations.localLength,
    Operations.subcircuits_witness,
    Operations.subcircuits_subcircuit, Operations.subcircuits_assert,
    Operations.subcircuits_nil, GeneralFormalCircuit.toSubcircuit_localLength,
    FormalAssertion.toSubcircuit_localLength, Readers.CPUState.circuit_localLength,
    MulOperation.circuit_localLength, Readers.RTypeReader.circuit_localLength,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, circuit_norm]
  exact Or.inr (Or.inr (Or.inl rfl))

end SP1Clean.MulChip
