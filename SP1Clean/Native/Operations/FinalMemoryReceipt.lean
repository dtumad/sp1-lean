import SP1Clean.Model.FinalMemoryValue
import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection

/-! # Finalizers retaining their original rows and publishing target-check receipts

The wrapper composes the original provider and publishes its full output record at the row's activity. It adds no
witness cells, assertions, or lookups. Every original channel is retained, so its ordered Memory
inventory can be projected without assuming that the appended target checks balance Memory.
-/

namespace SP1Clean.FinalMemoryReceipt

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime]
variable {Input : TypeMap} [ProvableType Input]

attribute [local circuit_norm] List.subset_append_left

/-- Publish the counted final-memory receipt from the bundled provider output. -/
@[circuit_norm]
def main (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg)
    (input : Var (ProvablePair Input field) (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let record ← provider input
  (FinalMemoryValue.channel ram).pushIf input.2 record
  return record

instance elaborated (ram : Bool)
    (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    ElaboratedCircuit (ZMod p) (ProvablePair Input field) MemoryMsg (main ram provider) where
  localLength := provider.localLength
  output := provider.output
  channelsWithGuarantees := provider.channelsWithGuarantees

def circuit (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg where
  name := provider.name
  main := main ram provider
  elaborated := elaborated ram provider
  Assumptions := provider.Assumptions
  Spec := provider.Spec
  ProverAssumptions := provider.ProverAssumptions
  channelsWithRequirements := provider.channelsWithRequirements ++ [(FinalMemoryValue.channel ram).toRaw]
  soundness := by
    circuit_proof_start [FinalMemoryValue.channel]
    exact ⟨h_holds h_assumptions, Or.inr h_assumptions⟩
  completeness := by
    circuit_proof_start [FinalMemoryValue.channel]
    exact h_assumptions

theorem width (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    (circuit ram provider).size = provider.size := rfl

theorem constraints (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    ((circuit ram provider).instantiate.operations 0).constraints =
      (provider.instantiate.operations 0).constraints := by
  simp only [circuit, circuit_norm, witnessAny, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat, FlatOperation.constraints, List.append_nil]

theorem lookups (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg) :
    ((circuit ram provider).instantiate.operations 0).lookups =
      (provider.instantiate.operations 0).lookups := by
  simp only [circuit, circuit_norm, witnessAny, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat, FlatOperation.lookups, List.append_nil]

/-- One physical receipt occurrence is appended, with the original activity and full output record. -/
theorem receipt_interactions (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg)
    (input : Var (ProvablePair Input field) (ZMod p)) (offset : ℕ) :
    (((circuit ram provider).main input).operations offset).interactionsWith (FinalMemoryValue.channel ram).toRaw =
      ((provider.main input).operations offset).interactionsWith (FinalMemoryValue.channel ram).toRaw ++
        [((FinalMemoryValue.channel ram).pushedIf input.2 (provider.output input offset)).toRaw] := by
  simp only [circuit, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions]
  rfl

theorem interactions (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) (ProvablePair Input field) MemoryMsg)
    (selected : RawChannel (ZMod p)) (different : selected ≠ (FinalMemoryValue.channel ram).toRaw) :
    ((circuit ram provider).instantiate.operations 0).interactionsWith selected =
      (provider.instantiate.operations 0).interactionsWith selected := by
  simp only [circuit, circuit_norm, witnessAny, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    FlatOperation.interactions, List.filter_append, List.filter_cons, List.filter_nil,
    ChannelInteraction.toRaw, Ne.symm different, ↓reduceIte, List.append_nil]

end SP1Clean.FinalMemoryReceipt
