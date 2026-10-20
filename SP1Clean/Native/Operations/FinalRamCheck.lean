import ToClean.Circuit.Guarded
import SP1Clean.FormalModel.Contracts.FinalRamCheck
import SP1Clean.Native.Operations.FinalMemoryChange
import SP1Clean.Native.Operations.FinalRamValue

/-! # Target RAM validation with selected change coverage

The existing eight-byte checker authenticates the whole target word. The selector contributes
only that record's RAM key; it cannot disable target checks or choose a different location.
A separate Boolean activity field guards the entire row for physical padding.
-/

namespace SP1Clean.FinalRamCheck

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose the complete target read and coverage on the same final RAM record. -/
def main (target : MemorySnapshot) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← FinalRamValue.circuit target input.record
  let _ ← FinalMemoryChange.circuit true ⟨input.record, input.selected⟩

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs unit (main target) := by elaborate_circuit

/-- Validate every RAM receipt, preserving its target-read Byte demand. -/
def activeCircuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.memory.check.ram.changes"
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input
  ProverAssumptions input data hint :=
    (FinalRamValue.circuit target).ProverAssumptions input.record data hint ∧
      FinalMemoryChange.Spec ⟨input.record, input.selected⟩
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
      ((FinalRamValue.main target input.record).operations offset).interactionValuesWith selected env ++
      ((FinalMemoryChange.main true ⟨input.record, input.selected⟩).operations
        (offset + (FinalRamValue.circuit target).localLength input.record)).interactionValuesWith selected env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FinalRamValue.circuit,
    FinalMemoryChange.circuit, List.filter_append, List.map_append, List.append_nil]

theorem receipt_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel true).toRaw env =
      [(FinalMemoryValue.channel true).pulledValue (eval env input.record)] := by
  rw [values, FinalRamValue.receipt_values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalMemoryChange.circuit (p := p) true).base (FinalMemoryValue.channel true).toRaw
    ⟨input.record, input.selected⟩
    (offset + (FinalRamValue.circuit target).localLength input.record) (by
      simp [FinalMemoryChange.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])
  simp only [FinalMemoryChange.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.append_nil]

theorem change_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith FinalMemoryChange.channel.toRaw env =
      [FinalMemoryChange.channel.pushedIfValue (eval env input.selected)
        (FinalMemoryChange.key true (eval env input.record))] := by
  rw [values, FinalMemoryChange.values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalRamValue.circuit target).base FinalMemoryChange.channel.toRaw input.record offset (by
      simp [FinalRamValue.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, byteChannel, Channel.toRaw])
  simp only [FinalRamValue.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.nil_append]

/-- The complete checker has no legacy lookup operations. -/
@[circuit_norm] theorem main_lookups (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) : ((main target input).operations offset).lookups = [] := by
  simp [main, FinalRamValue.circuit, FinalRamValue.main, FinalMemoryChange.circuit,
    FinalMemoryChange.main, assertBool, InitialMemoryRead.circuitNamed, InitialMemoryRead.main,
    InitialMemoryLookup.circuitNamed, InitialMemoryLookup.main_lookups,
    AddOperation.circuit, AddOperation.main, Gadgets.Equality.main, circuit_norm]

/-- Every checker channel supports zero activity, and assumed guarantees remain declared. -/
instance guardSupported (target : MemorySnapshot) : Guarded.Supported (activeCircuit (p := p) target) :=
  Guarded.Supported.of_emitted_requirements _
    (fun input offset => main_lookups target input offset)
    (by
      intro selected member
      simp only [GeneralFormalCircuit.channels, activeCircuit, FinalRamValue.circuit, circuit_norm] at member
      have registered : selected =
          (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw ∨
          selected = byteChannel.toRaw ∨ selected = (FinalMemoryValue.channel true).toRaw ∨
          selected = FinalMemoryChange.channel.toRaw := by
        simpa [InitialMemoryRead.circuitNamed_guarantees, List.mem_flatten,
          List.mem_replicate, or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro input offset selected member outside interaction occurs
      simp only [activeCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact False.elim (outside (by simp [activeCircuit, FinalRamValue.circuit, circuit_norm]))
      · change interaction ∈ ((main target input).operations offset).interactionsWith
          FinalMemoryChange.channel.toRaw at occurs
        have empty := InteractionRecovery.interactionsWith_main_eq_nil
          (FinalRamValue.circuit target).base FinalMemoryChange.channel.toRaw input.record offset (by
            simp [FinalRamValue.circuit, circuit_norm, FinalMemoryValue.channel,
              FinalMemoryChange.channel, byteChannel, Channel.toRaw, StaticTable.channel])
        simp only [FinalRamValue.circuit] at empty
        simp only [main, Operations.interactionsWith, circuit_norm,
          GeneralFormalCircuit.toSubcircuit_interactions, FinalMemoryChange.circuit,
          FinalMemoryChange.main, assertBool] at occurs
        simp only [Operations.interactionsWith] at empty
        simp only [FinalRamValue.circuit, List.filter_append, empty,
          FormalAssertion.toSubcircuit_interactions, circuit_norm] at occurs
        simp_all [circuit_norm])

/-- Boolean activity disables the entire target check and its receipt and change demands. -/
def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit (activeCircuit target) inferInstance

/-- Every physical row retains a receipt occurrence at its constrained activity. -/
theorem guarded_receipt_values (target : MemorySnapshot) (input : Var RowInput (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    (((circuit target).main input).operations offset).interactionValuesWith
        (FinalMemoryValue.channel true).toRaw env =
      [(FinalMemoryValue.channel true).pulledIfValue (env input.2) (eval env input.1.record)] := by
  change ((Guarded.main (activeCircuit target) (guardSupported target) input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [activeCircuit, receipt_values, List.map_cons, List.map_nil,
    Channel.pulledValue, Channel.pulledIfValue, mul_neg, mul_one]

/-- The effective coverage coefficient is activity times the independent change selector. -/
theorem guarded_change_values (target : MemorySnapshot) (input : Var RowInput (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    (((circuit target).main input).operations offset).interactionValuesWith FinalMemoryChange.channel.toRaw env =
      [FinalMemoryChange.channel.pushedIfValue (env input.2 * env input.1.selected)
        (FinalMemoryChange.key true (eval env input.1.record))] := by
  change ((Guarded.main (activeCircuit target) (guardSupported target) input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [activeCircuit, change_values, List.map_cons, List.map_nil, Channel.pushedIfValue]
  simp only [circuit_norm]

/-- Validate the final RAM record and select its contribution to the change inventory. -/
def populate? (source target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (RowInput (ZMod p)) :=
  (FinalRamValue.populate? target record).map fun value =>
    (⟨value, if MemoryMsg.locOf record ∈ source.changes target then 1 else 0⟩, 1)

theorem populate?_sound (source target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (input : RowInput (ZMod p)) (found : populate? source target record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input.1.record = record := by
  obtain ⟨value, checked, equal⟩ := Option.map_eq_some_iff.mp found
  obtain rfl := equal
  obtain ⟨valid, same⟩ := FinalRamValue.populate?_sound target record value checked data hint
  refine ⟨⟨Or.inr rfl, fun _ => ⟨valid, ?_⟩⟩, same⟩
  change (if MemoryMsg.locOf record ∈ source.changes target then (1 : ZMod p) else 0) = 0 ∨ _
  split <;> simp

end SP1Clean.FinalRamCheck
