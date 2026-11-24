import SP1Clean.Native.Operations.WriteEffects
import SP1Clean.Proofs.Operations.WriteBufferPhysical
import ToClean.Circuit.InteractionRecovery

/-! # Physical native WRITE effect request and complete word decoding

Both demand modes check the entire selected incoming receipt. A header is unique at its incoming
clock and a word uses its clock and absolute aligned byte address. Padding retains zero-weight
occurrences on the same private channels as the corresponding active rows.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem request_lookups (input : Var Request (ZMod p)) (offset : ℕ) :
    ((requestMain input).operations offset).lookups = [] := by
  simp [requestMain, WriteDescriptor.circuit, WriteDescriptor.main, WordRangeCheck.circuit,
    WordRangeCheck.main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main,
    Gadgets.IsZeroField.circuit, Gadgets.Equality.circuit, Gadgets.Equality.main, circuit_norm, Operations.lookups]

private theorem word_lookups (input : Var WordRow (ZMod p)) (offset : ℕ) :
    ((wordMain input).operations offset).lookups = [] := by
  simp [wordMain, U16toU8OperationSafe.circuit, U16toU8OperationSafe.main, circuit_norm, Operations.lookups]

/-- Full unguarded ledger of the request row. The deterministic classifier adds no interactions. -/
theorem request_interactions (r : Var Request (ZMod p)) (offset : Nat) (ch : RawChannel (ZMod p)) :
    ((requestMain r).operations offset).interactionsWith ch =
      [(WriteBuffer.effectHeaderChannel.pulled r.header).toRaw, (requestChannel.pushed r).toRaw].filter
        (fun i => decide (i.channel = ch)) := by
  have empty : (FlatOperation.interactions (WriteDescriptor.circuit.toSubcircuit offset r.header.descriptor).ops.toFlat).filter
      (fun i => decide (i.channel = ch)) = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    exact InteractionRecovery.interactionsWith_main_eq_nil WriteDescriptor.circuit.base ch _ _
      (by simp [WriteDescriptor.circuit, WriteDescriptor.elaborated, circuit_norm])
  simp only [requestMain, circuit_norm, empty, List.nil_append, List.filter_cons, List.filter_nil]

/-- The only transfers other than the shared SP1 Byte requests use the original read and its entire byte vector. -/
theorem word_interactions (r : Var WordRow (ZMod p)) (offset : Nat) (ch : RawChannel (ZMod p)) (other : ch ≠ byteChannel.toRaw) :
    ((wordMain r).operations offset).interactionsWith ch =
      [(WriteBuffer.wordChannel.pulled r.read).toRaw, (octetsChannel.pushed (r.octets (.const (256 : ZMod p)⁻¹))).toRaw].filter
        (fun i => decide (i.channel = ch)) := by
  have empty := InteractionRecovery.filter_interactions_formalAssertion_eq_nil U16toU8OperationSafe.circuit ch
    (n := offset) ⟨r.read.value, ⟨r.low⟩, 1⟩ (by simpa [U16toU8OperationSafe.circuit, circuit_norm] using other) List.not_mem_nil
  simp only [wordMain, circuit_norm, List.nil_append]
  simp only [Nat.add_zero, empty, List.nil_append, List.filter_cons, List.filter_nil, circuit_norm]

instance requestGuardSupported : Guarded.Supported (requestCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ request_lookups
    (by
      intro ch mem
      have known : ch = WriteBuffer.effectHeaderChannel.toRaw ∨ ch = requestChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, requestCircuit, requestElaborated, WriteDescriptor.circuit,
          WriteDescriptor.elaborated, circuit_norm, or_comm] using mem
      rcases known with rfl | rfl <;> infer_instance)
    (by
      intro input offset selected required _ interaction member
      obtain rfl := List.mem_singleton.mp required
      change interaction ∈ ((requestMain input).operations offset).interactionsWith requestChannel.toRaw at member
      rw [request_interactions] at member
      simp [WriteBuffer.effectHeaderChannel, requestChannel, circuit_norm] at member
      subst interaction
      rfl)

instance wordGuardSupported : Guarded.Supported (wordCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ word_lookups
    (by
      intro ch mem
      have known : ch = WriteBuffer.wordChannel.toRaw ∨ ch = byteChannel.toRaw ∨ ch = octetsChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, wordCircuit, wordElaborated, circuit_norm, or_assoc, or_comm, or_left_comm] using mem
      rcases known with rfl | rfl | rfl <;> infer_instance)
    (by
      intro input offset selected required _ interaction member
      obtain rfl := List.mem_singleton.mp required
      change interaction ∈ ((wordMain input).operations offset).interactionsWith octetsChannel.toRaw at member
      rw [word_interactions _ _ _ (by simp [octetsChannel, byteChannel, circuit_norm])] at member
      simp [WriteBuffer.wordChannel, octetsChannel, circuit_norm] at member
      subst interaction
      rfl)

/-- One guarded classification per header even when the buffer is empty or ignored. -/
def requestComponent : Component (ZMod p) where
  circuit := Guarded.circuit requestCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (requestCircuit (p := p)).name WriteBuffer.effectHeaderChannel .push
    (fun h => [WriteBuffer.hintKey h.clock]) (fun row => row.1.header) (fun row => row.2)
  Assumptions := (Guarded.circuit requestCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

/-- Decode every observed word independent of descriptor, preserving all partial-word lanes. -/
def wordComponent : Component (ZMod p) where
  circuit := Guarded.circuit wordCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (wordCircuit (p := p)).name WriteBuffer.wordChannel .push
    (fun r => [WriteBuffer.hintKey r.clock, WriteBuffer.hintKey r.key]) (fun row => row.1.read) (fun row => row.2)
  Assumptions := (Guarded.circuit wordCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

end SP1Clean.WriteEffects
