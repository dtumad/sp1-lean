import SP1Clean.FormalModel.Contracts.FinalRamCheck
import SP1Clean.Native.Operations.FinalMemoryChange
import SP1Clean.Native.Operations.FinalRamValue

/-! # Target RAM validation with selected change coverage

The existing eight-byte checker authenticates the whole target word. The selector contributes
only that record's RAM key; it cannot disable target checks or choose a different location.
-/

namespace SP1Clean.FinalRamCheck

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the complete target read and coverage on the same final RAM record. -/
def main (target : MemorySnapshot) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← FinalRamValue.circuit target input.value
  let _ ← FinalMemoryChange.circuit true ⟨input.value.record, input.selected⟩

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs unit (main target) := by elaborate_circuit

/-- Validate every RAM receipt, preserving its target-read Byte demand. -/
def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input
  ProverAssumptions input data hint :=
    (FinalRamValue.circuit target).ProverAssumptions input.value data hint ∧
      FinalMemoryChange.Spec ⟨input.value.record, input.selected⟩
  channelsWithRequirements := [(FinalMemoryValue.channel true).toRaw, FinalMemoryChange.channel.toRaw]
  soundness := by
    circuit_proof_start [FinalRamValue.circuit, FinalMemoryChange.circuit]
    exact h_holds
  completeness := by
    circuit_proof_start [FinalRamValue.circuit, FinalMemoryChange.circuit]
    exact h_assumptions

/-- The target read's Byte demand and the selector's receipt remain in the same physical row. -/
theorem values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) (selected : RawChannel (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith selected env =
      ((FinalRamValue.main target input.value).operations offset).interactionValuesWith selected env ++
      ((FinalMemoryChange.main true ⟨input.value.record, input.selected⟩).operations
        (offset + (FinalRamValue.circuit target).localLength input.value)).interactionValuesWith selected env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FinalRamValue.circuit,
    FinalMemoryChange.circuit, List.filter_append, List.map_append, List.append_nil]

theorem receipt_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel true).toRaw env =
      [(FinalMemoryValue.channel true).pulledValue (eval env input.value.record)] := by
  rw [values, FinalRamValue.receipt_values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalMemoryChange.circuit (p := p) true).base (FinalMemoryValue.channel true).toRaw
    ⟨input.value.record, input.selected⟩
    (offset + (FinalRamValue.circuit target).localLength input.value) (by
      simp [FinalMemoryChange.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])
  simp only [FinalMemoryChange.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.append_nil]

theorem change_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith FinalMemoryChange.channel.toRaw env =
      [FinalMemoryChange.channel.pushedIfValue (eval env input.selected)
        (FinalMemoryChange.key true (eval env input.value.record))] := by
  rw [values, FinalMemoryChange.values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalRamValue.circuit target).base FinalMemoryChange.channel.toRaw input.value offset (by
      simp [FinalRamValue.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, byteChannel, Channel.toRaw])
  simp only [FinalRamValue.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.nil_append]

/-- The existing target RAM constructor supplies every interval and byte witness. -/
def populate? (source target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (Inputs (ZMod p)) :=
  (FinalRamValue.populate? target record).map fun value =>
    ⟨value, if MemoryMsg.locOf record ∈ source.changes target then 1 else 0⟩

theorem populate?_sound (source target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (input : Inputs (ZMod p)) (found : populate? source target record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input.value.record = record := by
  obtain ⟨value, checked, equal⟩ := Option.map_eq_some_iff.mp found
  obtain rfl := equal
  obtain ⟨valid, same⟩ := FinalRamValue.populate?_sound target record value checked data hint
  refine ⟨⟨valid, ?_⟩, same⟩
  change (if MemoryMsg.locOf record ∈ source.changes target then (1 : ZMod p) else 0) = 0 ∨ _
  split <;> simp

end SP1Clean.FinalRamCheck
