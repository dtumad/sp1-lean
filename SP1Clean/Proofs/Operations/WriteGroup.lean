import SP1Clean.Native.Operations.WriteGroup
import SP1Clean.Native.Operations.WriteSliceSource
import SP1Clean.Proofs.Operations.WriteEffects
import ToClean.Circuit.EmptyChannelInterface
import ToClean.Air.Footprint

/-! # Complete grouped WRITE table and its physical ledger

The two read sites retain multiplicity zero for absent blocks. The word itself and its fixed
selection plan are always consumed. All coordinate arithmetic and all eight comparison lanes
emit no other physical interaction.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

private theorem no_coordinates (r : Var Group (ZMod p)) (n : Nat) :
    FlatOperation.interactions (groupCoordinatesCircuit.toSubcircuit n r).ops.toFlat = [] := by
  rw [GeneralFormalCircuit.toSubcircuit_interactions]
  apply groupCoordinatesCircuit.base.interactions_eq_nil_of_channels_eq_nil
  simp [FormalCircuitBase.channels, groupCoordinatesCircuit,groupCoordinatesElaborated,circuit_norm]

omit [Fact (2^17 < p)] in
private theorem no_comparison (r : Var Group (ZMod p)) (n : Nat) :
    FlatOperation.interactions (groupBytesCircuit.toSubcircuit n r).ops.toFlat = [] := by
  rw [FormalAssertion.toSubcircuit_interactions]
  apply groupBytesCircuit.base.interactions_eq_nil_of_channels_eq_nil
  simp [FormalCircuitBase.channels,groupBytesCircuit,groupBytesElaborated,circuit_norm]

/-- This is the complete unfiltered ledger. No SP1 Byte occurrences remain on the grouped word. -/
theorem group_ledger (r : Var Group (ZMod p)) (n : Nat) :
    ((groupMain r).operations n).interactions =
      [(octetsChannel.pulled r.octets).toRaw, (sliceChannel.pulled r.plan).toRaw,
       (positionChannel.pulledIf r.plan.nonempty r.previous).toRaw, (blockChannel.pulledIf r.leftGate (r.block false)).toRaw,
       (blockChannel.pulledIf r.rightGate (r.block true)).toRaw, (positionChannel.pushedIf r.plan.nonempty r.next).toRaw] := by
  have noZero (x : Expression (ZMod p)) (off : Nat) :
      FlatOperation.interactions (Gadgets.IsZeroField.circuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [FormalCircuit.toSubcircuit_interactions]
    apply Gadgets.IsZeroField.circuit.base.interactions_eq_nil_of_channels_eq_nil
    rfl
  have noRange (x : Expression (ZMod p)) (off : Nat) (fits : 2^4 < p) :
      FlatOperation.interactions ((Gadgets.ToBits.rangeCheck 4 fits).toSubcircuit off x).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    apply (Gadgets.ToBits.rangeCheck 4 fits).base.interactions_eq_nil_of_channels_eq_nil
    rfl
  simp only [groupMain,circuit_norm,no_coordinates,no_comparison,noZero,noRange,List.nil_append]
  simp only [FormalAssertion.toSubcircuit_interactions,circuit_norm,List.nil_append,Operations.interactions]

private theorem group_lookups (r : Var Group (ZMod p)) (n : Nat) :
    ((groupMain r).operations n).lookups = [] := by
  simp [groupMain,groupCoordinatesCircuit,groupCoordinatesMain,groupBytesCircuit,groupBytesMain,AddressDiv8.circuit,AddressDiv8.main,
    AddressSum.circuit,AddressSum.main,WordRangeCheck.circuit,WordRangeCheck.main,Gadgets.Equality.circuit,Gadgets.Equality.main,
    Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Gadgets.IsZeroField.circuit,circuit_norm,Operations.lookups,List.ofFn_succ]

instance groupGuardSupported : Guarded.Supported (groupCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ group_lookups
    (by
      intro ch mem
      have known : ch = octetsChannel.toRaw ∨ ch = sliceChannel.toRaw ∨ ch = positionChannel.toRaw ∨ ch = blockChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels,groupCircuit,groupElaborated,groupCoordinatesCircuit,groupCoordinatesElaborated,
          groupBytesCircuit,groupBytesElaborated,AddressSum.circuit,AddressSum.elaborated,AddressDiv8.circuit,AddressDiv8.elaborated,
          circuit_norm,List.ofFn_succ,or_comm,or_assoc,or_left_comm] using mem
      rcases known with rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro r n ch required outside
      simp only [groupCircuit,List.mem_cons,List.not_mem_nil,or_false] at required
      rcases required with rfl | rfl <;> exact False.elim (outside (by simp [groupCircuit,groupElaborated,circuit_norm])))

/-- Every enabled physical placement has its semantic coordinates, checked lane correspondence
and Boolean block gates. The interior input channels carry unconditional local guarantees. -/
theorem guarded_group_valid (r : Var (ProvablePair Group field) (ZMod p)) (n : Nat) (env : Environment (ZMod p))
    (checked : (((Guarded.circuit groupCircuit inferInstance).main r).operations n).ConstraintsHold env) :
    IsBool (eval env r).2 ∧ ((eval env r).2 = 1 → (eval env r).1.Valid) := by
  let g := Guarded.circuit (groupCircuit (p := p)) inferInstance
  apply (g.original_full_soundness n env r (fun _ => trivial) checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (g.in_channels_or_guarantees_full r n env)]
  intro ch member
  have known : ch = octetsChannel.toRaw ∨ ch = sliceChannel.toRaw ∨ ch = positionChannel.toRaw ∨ ch = blockChannel.toRaw := by
    simpa [g,groupCircuit,groupElaborated,groupCoordinatesCircuit,groupCoordinatesElaborated,
      groupBytesCircuit,groupBytesElaborated,AddressSum.circuit,AddressSum.elaborated,AddressDiv8.circuit,AddressDiv8.elaborated,
      circuit_norm,List.ofFn_succ,or_comm,or_assoc,or_left_comm] using member
  rcases known with rfl | rfl | rfl | rfl
  · exact Operations.channelGuarantees_of_trivial _ (by simp [octetsChannel,Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [sliceChannel,Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [positionChannel,Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [blockChannel,Channel.toRaw]) _ _

/-- Exactly one grouped placement per authentic word, irrespective of dispatch or payload size. -/
def groupComponent : Component (ZMod p) where
  circuit := Guarded.circuit groupCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (groupCircuit (p := p)).name octetsChannel .push
    (fun r => [WriteBuffer.hintKey r.clock,WriteBuffer.hintKey r.key]) (fun r => r.1.octets) (fun r => r.2)
  Assumptions := (Guarded.circuit groupCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

/-- The guard preserves the underlying channel of every active or padded occurrence. -/
theorem group_channels :
    (groupComponent (p := p)).operations.interactions.map (·.channel) =
    [octetsChannel.toRaw,sliceChannel.toRaw,positionChannel.toRaw,blockChannel.toRaw,blockChannel.toRaw,positionChannel.toRaw] := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,groupComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  change (((groupMain _).operations _).interactions.map _).map _ = _
  rw [group_ledger]
  rfl

end SP1Clean.WriteEffects
