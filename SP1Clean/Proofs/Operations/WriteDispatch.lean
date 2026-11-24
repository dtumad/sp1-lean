import SP1Clean.Native.Operations.WriteDispatch
import SP1Clean.Proofs.Operations.WriteEffects

/-! # Physical chronological WRITE dispatch

Demand is keyed by the complete incoming ECALL time. The entire classification receipt is
compared, and every inactive row preserves all fixed interaction sites with zero multiplicity.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- All private dispatch receipts in physical order. Only the arithmetic subcircuits use SP1 Byte. -/
theorem dispatch_ledger (r : Var Dispatch (ZMod p)) (n : Nat) (ch : RawChannel (ZMod p)) (other : ch ≠ Channels.byteChannel.toRaw) :
    ((dispatchMain r).operations n).interactionsWith ch =
    [(requestChannel.pulled r.request).toRaw, (cursorChannel.pulled r.previous).toRaw,
     (recordChannel.pulledIf r.flags.hook (r.metadata 2 #v[r.request.route,0,0])).toRaw,
     (recordChannel.pulledIf r.flags.hook (r.metadata 0 r.length)).toRaw,
     (recordChannel.pulledIf r.flags.hook (r.metadata 3 r.returned)).toRaw,
     (queueEffectChannel.pushedIf (r.flags.direct + r.flags.hook) (r.ticket r.flags)).toRaw,
     (positionChannel.pushed (r.start r.flags)).toRaw, (positionChannel.pulled (r.finish r.flags)).toRaw,
     (cursorChannel.pushed (r.next r.flags)).toRaw].filter (fun i => decide (i.channel = ch)) := by
  have sum (x : Var AddressSum.Inputs (ZMod p)) (off : Nat) :
      (FlatOperation.interactions (AddressSum.circuit.toSubcircuit off x).ops.toFlat).filter (fun i => decide (i.channel = ch)) = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    change (((AddressSum.main x).operations off).interactions.filter _) = []
    rw [AddressSum.interactions]
    rfl
  have pred (x : Var WriteStart.Inputs (ZMod p)) (off : Nat) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil WriteStart.circuit ch x
      (by simpa [WriteStart.circuit, WriteStart.elaborated, circuit_norm] using other) List.not_mem_nil (n := off)
  have flags (x : Expression (ZMod p)) (off : Nat) :
      (FlatOperation.interactions (flagsCircuit.toSubcircuit off x).ops.toFlat).filter (fun i => decide (i.channel = ch)) = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    apply InteractionRecovery.interactionsWith_main_eq_nil flagsCircuit.base
    simp [flagsCircuit, flagsElaborated, circuit_norm]
  simp only [dispatchMain, circuit_norm, List.nil_append, sum, pred, flags]
  simp [FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.circuit, Gadgets.Equality.main,
    circuit_norm, List.filter_cons]

private theorem dispatch_lookups (r : Var Dispatch (ZMod p)) (n : Nat) : ((dispatchMain r).operations n).lookups = [] := by
  simp [dispatchMain, AddressSum.circuit, AddressSum.main, WordRangeCheck.circuit, WordRangeCheck.main,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Gadgets.IsZeroField.circuit,
    Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Operations.lookups, circuit_norm,
    flagsCircuit, flagsMain, WriteStart.circuit, WriteStart.main, AddOperation.circuit, AddOperation.main]

instance dispatchGuardSupported : Guarded.Supported (dispatchCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ dispatch_lookups
    (by
      intro ch mem
      have known : ch = requestChannel.toRaw ∨ ch = cursorChannel.toRaw ∨ ch = Channels.byteChannel.toRaw ∨
          ch = recordChannel.toRaw ∨ ch = queueEffectChannel.toRaw ∨ ch = positionChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, dispatchCircuit, dispatchElaborated, flagsCircuit, flagsElaborated,
          AddressSum.circuit, AddressSum.elaborated, WriteStart.circuit, WriteStart.elaborated,
          circuit_norm, or_assoc, or_comm, or_left_comm] using mem
      rcases known with rfl | rfl | rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro r n ch required outside act member
      have onlyQueue : ch = queueEffectChannel.toRaw := by
        simp only [dispatchCircuit, List.mem_cons, List.not_mem_nil, or_false] at required
        rcases required with rfl | rfl | rfl | rfl
        · exact False.elim (outside (by simp [dispatchCircuit, dispatchElaborated, circuit_norm]))
        · rfl
        · exact False.elim (outside (by simp [dispatchCircuit, dispatchElaborated, circuit_norm]))
        · exact False.elim (outside (by simp [dispatchCircuit, dispatchElaborated, circuit_norm]))
      subst ch
      change act ∈ ((dispatchMain r).operations n).interactionsWith queueEffectChannel.toRaw at member
      rw [dispatch_ledger _ _ _ (by simp [queueEffectChannel, Channels.byteChannel, circuit_norm])] at member
      simp [requestChannel, cursorChannel, queueEffectChannel, recordChannel, positionChannel, circuit_norm] at member
      subst act
      rfl)

/-- One genuine dispatch for each classified physical header, including every empty write. -/
def dispatchComponent : Component (ZMod p) where
  circuit := Guarded.circuit dispatchCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (dispatchCircuit (p := p)).name requestChannel .push
    (fun r => [WriteBuffer.hintKey r.header.clock]) (fun r => r.1.request) (fun r => r.2)
  Assumptions := (Guarded.circuit dispatchCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

end SP1Clean.WriteEffects
