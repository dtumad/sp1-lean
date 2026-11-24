import SP1Clean.Native.Operations.WriteLanes
import SP1Clean.Native.Operations.WriteByteStep
import ToClean.Circuit.SubcircuitProjection

/-! # Guarded physical placement of WRITE bytes

Every decoded word retains eight gated lane occurrences with the original address and clock.
The byte walker consumes the lane at its next absolute address.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical

variable {p : Nat} [Fact p.Prime]

/-- The lane ledger includes all eight positions regardless of the asserted masks. -/
theorem lane_ledger (r : Var LaneRow (ZMod p)) (n : Nat) :
    ((laneMain r).operations n).interactions = (octetsChannel.pulled r.octets).toRaw ::
      List.ofFn (fun i : Fin 8 => (byteChannel.pushedIf r.selected[i] (r.lane i (.const i.val))).toRaw) := by
  simp [laneMain, circuit_norm, List.ofFn_succ, FormalAssertion.toSubcircuit_interactions, Operations.interactions]

instance laneGuardSupported : Guarded.Supported (laneCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ (by
    intro r n
    change ((laneMain r).operations n).lookups = []
    simp [laneMain, circuit_norm, List.ofFn_succ, Operations.lookups])
    (by
      intro ch mem
      have known : ch = octetsChannel.toRaw ∨ ch = byteChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, laneCircuit, laneElaborated, circuit_norm, List.ofFn_succ, or_comm] using mem
      rcases known with rfl | rfl <;> infer_instance)
    (by
      intro r n ch required _ act member
      obtain rfl := List.mem_singleton.mp required
      change act ∈ (((laneMain r).operations n).interactions.filter _) at member
      rw [lane_ledger] at member
      simp only [List.mem_filter, List.mem_cons, List.mem_ofFn] at member
      obtain ⟨same | ⟨i,rfl⟩, hasChannel⟩ := member
      · subst act
        simp [octetsChannel, byteChannel, circuit_norm] at hasChannel
      · rfl)

/-- One compulsory lane-selection row per actual word, padded by Clean's standard guard. -/
def laneComponent : Component (ZMod p) where
  circuit := Guarded.circuit laneCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (laneCircuit (p := p)).name octetsChannel .push
    (fun r => [WriteBuffer.hintKey r.clock, WriteBuffer.hintKey r.key]) (fun r => r.1.octets) (fun r => r.2)
  Assumptions := (Guarded.circuit laneCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

variable [Fact (2^17 < p)]

/-- Away from the SP1 Byte range chip, this is the entire position-row ledger. -/
theorem byteStep_ledger (r : Var ByteStep (ZMod p)) (n : Nat) (ch : RawChannel (ZMod p))
    (other : ch ≠ Channels.byteChannel.toRaw) :
    ((byteStepMain r).operations n).interactionsWith ch =
      [(positionChannel.pulled r.previous).toRaw, (byteChannel.pulled r.read).toRaw,
       (recordChannel.pulledIf (1 - r.ignored - r.direct) r.record).toRaw,
       (nodeByteChannel.pushedIf r.direct r.nodeByte).toRaw, (positionChannel.pushed r.next).toRaw].filter
        (fun a => decide (a.channel = ch)) := by
  have sum (x : Var AddressSum.Inputs (ZMod p)) (off : Nat) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddressSum.circuit ch x
      (by simpa [AddressSum.circuit, AddressSum.elaborated, circuit_norm] using other) List.not_mem_nil (n := off)
  simp only [byteStepMain, circuit_norm, sum, List.nil_append]
  simp [Gadgets.IsZeroField.circuit, circuit_norm, List.filter_cons]

private theorem byteStep_lookups (r : Var ByteStep (ZMod p)) (n : Nat) : ((byteStepMain r).operations n).lookups = [] := by
  simp [byteStepMain, AddressSum.circuit, AddressSum.main, WordRangeCheck.circuit, WordRangeCheck.main,
    AddrAddOperation.circuit, AddrAddOperation.main, Gadgets.Equality.main, Gadgets.IsZeroField.circuit,
    Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Operations.lookups, circuit_norm]

instance byteStepGuardSupported : Guarded.Supported (byteStepCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ byteStep_lookups
    (by
      intro ch mem
      have known : ch = positionChannel.toRaw ∨ ch = byteChannel.toRaw ∨ ch = Channels.byteChannel.toRaw ∨
          ch = recordChannel.toRaw ∨ ch = nodeByteChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, byteStepCircuit, byteStepElaborated, AddressSum.circuit, AddressSum.elaborated,
          circuit_norm, or_assoc, or_comm, or_left_comm] using mem
      rcases known with rfl | rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro r n ch required outside act member
      have onlyNode : ch = nodeByteChannel.toRaw := by
        simp only [byteStepCircuit, List.mem_cons, List.not_mem_nil, or_false] at required
        rcases required with rfl | rfl | rfl
        · exact False.elim (outside (by simp [byteStepCircuit, byteStepElaborated, circuit_norm]))
        · rfl
        · exact False.elim (outside (by simp [byteStepCircuit, byteStepElaborated, circuit_norm]))
      subst ch
      change act ∈ ((byteStepMain r).operations n).interactionsWith nodeByteChannel.toRaw at member
      rw [byteStep_ledger _ _ _ (by simp [nodeByteChannel, Channels.byteChannel, circuit_norm])] at member
      simp [positionChannel, byteChannel, recordChannel, nodeByteChannel, circuit_norm] at member
      subst act
      rfl)

/-- Each selected guest byte pays for exactly one position step, including ignored output. -/
def byteStepComponent : Component (ZMod p) where
  circuit := Guarded.circuit byteStepCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (byteStepCircuit (p := p)).name byteChannel .push
    (fun r => [WriteBuffer.hintKey r.clock, WriteBuffer.hintKey r.key]) (fun r => r.1.read) (fun r => r.2)
  Assumptions := (Guarded.circuit byteStepCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

end SP1Clean.WriteEffects
