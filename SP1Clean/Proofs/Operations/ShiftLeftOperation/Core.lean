import ToClean.Gadgets.Equality
import SP1Clean.Native.Operations.ShiftLeftOperation.Core
import ToClean.Circuit.InteractionRecovery
import Clean.Utils.Tactics

/-! # `ShiftLeftCore` — proof boundary for ShiftLeft's assertion tail

The native circuit emits the chip-local constraint tail. Its folded public contract is
`ShiftLeftChip.CoreSpec`, so parent proofs need not repeatedly normalize the full assertion list.
-/

namespace SP1Clean.ShiftLeftCore

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The assertion block has no semantic precondition. -/
def Assumptions (_ : ShiftLeftChip.Columns (ZMod p)) : Prop := True

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) main Assumptions ShiftLeftChip.CoreSpec := by
  circuit_proof_start [ShiftLeftChip.CoreSpec]
  exact h_holds

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) main Assumptions ShiftLeftChip.CoreSpec := by
  circuit_proof_start [ShiftLeftChip.CoreSpec]
  exact h_spec

/-- The zero-witness ShiftLeft chip-local tail as a Clean `FormalAssertion`. -/
def circuit : FormalAssertion (ZMod p) ShiftLeftChip.Columns where
  main
  elaborated
  computableWitnesses := by
    intro n input env env'
    simp only [main, circuit_norm, Nat.add_zero,
      Gadgets.Equality.toSubcircuit_computableWitnesses, ProverEnvironment.OnlyAccessedBelow]
  Assumptions := Assumptions
  Spec := ShiftLeftChip.CoreSpec
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (cols : Var ShiftLeftChip.Columns (ZMod p)) :
    circuit.localLength cols = 0 := rfl

omit [Fact (2 ^ 17 < p)] in
/-- The assertion-only core contributes no interaction on any channel when composed. -/
theorem interactionsWith_subcircuit_eq_nil (channel : RawChannel (ZMod p))
    (cols : Var ShiftLeftChip.Columns (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith channel
        (.subcircuit (circuit.toSubcircuit offset cols) :: ops) =
      Operations.interactionsWith channel ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
    circuit channel cols ops List.not_mem_nil List.not_mem_nil

end SP1Clean.ShiftLeftCore
