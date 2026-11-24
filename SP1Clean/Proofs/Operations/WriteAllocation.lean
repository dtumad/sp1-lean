import SP1Clean.Native.Operations.WriteAllocation
import SP1Clean.Proofs.Operations.WriteBufferPhysical

/-! # Physical demand tables for allocating WRITE calls

Only a complete ticket creates a call row. A node row is keyed by its complete incoming
cursor and hash-free clock and remaining-count indices. At zero remaining the call's own
terminal pull consumes the last cursor, including for a hook with no returned buffers.
-/

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat WriteEffects
open scoped Classical

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)] [Fact (2^24 < p)] [Fact (2^25 < p)]

omit [Fact (2^17 < p)] in
/-- These five transfers comprise the full call ledger. The timestamp checks are lookup-free. -/
theorem open_ledger (r : Var Open (ZMod p)) (n : Nat) (ch : RawChannel (ZMod p)) :
    ((openMain r).operations n).interactionsWith ch =
      [(queueEffectChannel.pulled r.ticket).toRaw,(HostHintQueue.stateChannel.pulled r.previous).toRaw,
       (cursorChannel.pushed r.first).toRaw,(cursorChannel.pulled r.last).toRaw,
       (HostHintQueue.stateChannel.pushed r.outgoing).toRaw].filter (fun i => decide (i.channel = ch)) := by
  have parts (v : Var ClockParts (ZMod p)) (m : Nat) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil ClockParts.circuit ch v
      (by simp [ClockParts.circuit, ClockParts.elaborated,circuit_norm]) List.not_mem_nil (n := m)
  have clock (v : Var ClockOrder.Inputs (ZMod p)) (m : Nat) :
      (FlatOperation.interactions (ClockOrder.circuit.toSubcircuit m v).ops.toFlat).filter (fun i => decide (i.channel = ch)) = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    apply InteractionRecovery.interactionsWith_main_eq_nil ClockOrder.circuit.base
    simp [ClockOrder.circuit,ClockOrder.elaborated,circuit_norm]
  simp only [openMain,circuit_norm,parts,clock,List.nil_append]
  simp [FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.circuit,Gadgets.Equality.main,circuit_norm,List.filter_cons]

omit [Fact (2^24 < p)] [Fact (2^25 < p)] in
/-- A node publishes its actual immutable metadata and issues one contents demand. All
additional transfers of the verified arithmetic subcircuit are on the released Byte bus. -/
theorem step_ledger (r : Var Step (ZMod p)) (n : Nat) (ch : RawChannel (ZMod p)) (other : ch ≠ Channels.byteChannel.toRaw) :
    ((stepMain r).operations n).interactionsWith ch =
      [(cursorChannel.pulled r.before).toRaw,(recordChannel.pulledIf (1-r.direct) r.metadata).toRaw,
       (HostHintQueue.nodeChannel.emitted r.readers r.node.node).toRaw,(contentsChannel.pushed r.contents).toRaw,
       (cursorChannel.pushed r.after).toRaw].filter (fun i => decide (i.channel = ch)) := by
  have node (v : Var HintNodeAllocate.Inputs (ZMod p)) (m : Nat) :
      (FlatOperation.interactions (HintNodeAllocate.circuit.toSubcircuit m v).ops.toFlat).filter (fun i => decide (i.channel = ch)) = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    exact HintNodeAllocate.main_other_interactions _ other _ _
  have sum (v : Var AddressSum.Inputs (ZMod p)) (m : Nat) :
      (FlatOperation.interactions (AddressSum.circuit.toSubcircuit m v).ops.toFlat).filter (fun i => decide (i.channel = ch)) = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    change (((AddressSum.main v).operations m).interactions.filter _) = []
    rw [AddressSum.interactions]
    rfl
  simp only [stepMain,circuit_norm,node,sum,List.nil_append]
  simp [FormalAssertion.toSubcircuit_interactions,circuit_norm,List.filter_cons]

/-- Both guard variants preserve the exact occurrence inventory on padded rows. -/
instance openSupported : Guarded.Supported (openCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro r m; change ((openMain r).operations m).lookups = []; simp [openMain,ClockParts.circuit,ClockParts.main,ClockOrder.circuit,ClockOrder.main,
         Gadgets.IsZeroField.circuit,Gadgets.Equality.circuit,Gadgets.Equality.main,
         Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Operations.lookups,circuit_norm])
    (by
      intro ch h
      have known : ch = queueEffectChannel.toRaw ∨ ch = HostHintQueue.stateChannel.toRaw ∨ ch = cursorChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels,openCircuit,openElaborated,ClockOrder.circuit,ClockOrder.elaborated,
          circuit_norm,or_comm,or_assoc,or_left_comm] using h
      rcases known with rfl|rfl|rfl <;> infer_instance)
    (by
      intro r m ch req outside
      simp only [openCircuit,List.mem_cons,List.not_mem_nil,or_false] at req
      rcases req with rfl|rfl <;> exact False.elim (outside (by simp [openCircuit,openElaborated,circuit_norm])))

instance stepSupported : Guarded.Supported (stepCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro r m; change ((stepMain r).operations m).lookups = []; simp [stepMain,HintNodeAllocate.circuit,HintNodeAllocate.main,AddressOrder.circuit,AddressOrder.main,
      AddrAddOperation.circuit,AddrAddOperation.main,AddressSum.circuit,AddressSum.main,WordRangeCheck.circuit,
      WordRangeCheck.main,Gadgets.IsZeroField.circuit,Gadgets.Equality.circuit,Gadgets.Equality.main,
      Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Operations.lookups,circuit_norm])
    (by
      intro ch h
      have known : ch = Channels.byteChannel.toRaw ∨ ch = cursorChannel.toRaw ∨ ch = recordChannel.toRaw ∨
          ch = HostHintQueue.nodeChannel.toRaw ∨ ch = contentsChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels,stepCircuit,stepElaborated,HintNodeAllocate.circuit,
          HintNodeAllocate.elaborated,AddrAddOperation.circuit,AddressOrder.circuit,AddressOrder.elaborated,AddressSum.circuit,
          AddressSum.elaborated,circuit_norm,or_comm,or_assoc,or_left_comm] using h
      rcases known with rfl|rfl|rfl|rfl|rfl <;> infer_instance)
    (by
      intro r m ch req outside i member
      simp only [stepCircuit,List.mem_cons,List.not_mem_nil,or_false] at req
      rcases req with rfl|rfl|rfl|rfl
      · exact False.elim (outside (by simp [stepCircuit,stepElaborated,circuit_norm]))
      · change i ∈ ((stepMain r).operations m).interactionsWith HostHintQueue.nodeChannel.toRaw at member
        rw [step_ledger _ _ _ (by simp [HostHintQueue.nodeChannel, Channels.byteChannel,circuit_norm])] at member
        simp [cursorChannel,recordChannel,HostHintQueue.nodeChannel,contentsChannel,circuit_norm] at member
        subst i
        rfl
      · change i ∈ ((stepMain r).operations m).interactionsWith contentsChannel.toRaw at member
        rw [step_ledger _ _ _ (by simp [contentsChannel, Channels.byteChannel,circuit_norm])] at member
        simp [cursorChannel,recordChannel,HostHintQueue.nodeChannel,contentsChannel,circuit_norm] at member
        subst i
        rfl
      · exact False.elim (outside (by simp [stepCircuit,stepElaborated,circuit_norm])))

/-- One row per matched allocation ticket, including an empty hook reply. -/
def openComponent : Component (ZMod p) where
  circuit := Guarded.circuit openCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (openCircuit (p := p)).name queueEffectChannel .push
    (fun ticket => [WriteBuffer.hintKey ticket.clock]) (fun r => r.1.ticket) (fun r => r.2)
  Assumptions := (Guarded.circuit openCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

/-- Each nonterminal cursor selects its one genuine fresh-node input. -/
def stepComponent : Component (ZMod p) where
  circuit := Guarded.circuit stepCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (stepCircuit (p := p)).name cursorChannel .push
    (fun s => [s.state.clk_high.val * 16777216 + s.state.clk_low.val,WriteBuffer.hintKey s.remaining])
    (fun r => r.1.before) (fun r => r.2)
  Assumptions := (Guarded.circuit stepCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

end SP1Clean.WriteAllocation
