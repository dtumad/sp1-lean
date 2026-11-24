import SP1Clean.Native.Operations.WriteAllocationWords
import SP1Clean.Proofs.Operations.WriteBufferPhysical
import ToClean.Circuit.EmptyChannelInterface
import ToClean.Air.Footprint

/-! # Physical immutable WRITE allocation contents

The node opens a mandatory walk. Every word emits a persistent queue record and carries both
private block occurrences, including zero-weight occurrences for padding and unused modes.
-/

namespace SP1Clean.WriteAllocation.Words
open Circuit Air.Flat WriteEffects
open scoped Classical

variable {p : Nat} [Fact p.Prime]

/-- A physical contents authorization opens its own padded word walk. -/
theorem seed_ledger (r : Var Contents (ZMod p)) (n : Nat) :
    ((seedMain r).operations n).interactions = [(contentsChannel.pulled r).toRaw,(cursorChannel.pushed (start r)).toRaw] := by
  simp [seedMain,circuit_norm]

/-- Every interface of the seed row remains sound under demand-table padding. -/
instance seedSupported : Guarded.Supported (seedCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (by intro r n; rfl)
    (by
      intro ch mem
      have h : ch = contentsChannel.toRaw ∨ ch = cursorChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels,seedCircuit,seedMain,circuit_norm] using mem
      rcases h with rfl|rfl <;> infer_instance)
    (by
      intro r n ch req outside i member
      simp only [seedCircuit,List.mem_cons,List.not_mem_nil,or_false] at req
      subst ch
      change i ∈ (((seedMain r).operations n).interactions.filter _) at member
      rw [seed_ledger] at member
      simp [contentsChannel,cursorChannel,circuit_norm] at member
      subst i
      rfl)

/-- The actual demand index selects an exact fresh contents authorization. -/
def seedComponent : Component (ZMod p) where
  circuit := Guarded.circuit seedCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (seedCircuit (p := p)).name contentsChannel .push
    (fun c => [WriteBuffer.hintKey c.pointer]) (fun r => r.1) (fun r => r.2)
  Assumptions := (Guarded.circuit seedCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

variable [Fact (2^17 < p)]

/-- All five sites in physical order, including each zero weight. The first auxiliary is the
row-constrained product of directness, occupancy and the grouped reads of this block. -/
theorem word_ledger (r : Var Row (ZMod p)) (n : Nat) :
    ((wordMain r).operations n).interactions =
      [(cursorChannel.pulled r.prior).toRaw,(blockChannel.pulledIf r.hookGate r.returned).toRaw,
       (blockChannel.emitted (var ⟨n⟩) r.direct).toRaw,(HostHintQueue.wordChannel.emitted r.wordReads r.word).toRaw,
       (cursorChannel.pushedIf r.payload.more r.next).toRaw] := by
  have payload (v : Var Payload (ZMod p)) (m : Nat) :
      FlatOperation.interactions (payloadCircuit.toSubcircuit m v).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    apply payloadCircuit.base.interactions_eq_nil_of_channels_eq_nil
    simp [FormalCircuitBase.channels,payloadCircuit,payloadElaborated,circuit_norm]
  have sum (v : Var AddressSum.Inputs (ZMod p)) (m : Nat) :
      FlatOperation.interactions (AddressSum.circuit.toSubcircuit m v).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    exact AddressSum.interactions v m
  simp only [wordMain,circuit_norm,payload,sum,List.nil_append,List.ofFn_succ]
  simp only [FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.circuit,Gadgets.Equality.main,Operations.interactions,circuit_norm,List.nil_append]

/-- The direct block multiplicity in the actual raw ledger is the checked product of the
source selector, live first lane and read count. It vanishes for every hook or padding word. -/
theorem word_supply (r : Var Row (ZMod p)) (n : Nat) (env : Environment (ZMod p))
    (checked : ((wordMain r).operations n).ConstraintsHold env) :
    (var ⟨n⟩ : Expression (ZMod p)).eval env = (r.directGate * r.blockReads).eval env := by
  have first : ((wordMain r).operations n).constraints[0]? = some (var ⟨n⟩ - r.directGate * r.blockReads) := by
    simp only [wordMain,circuit_norm,FormalAssertion.toSubcircuit_toFlat,Gadgets.Equality.circuit,Gadgets.Equality.main,Operations.constraints,FlatOperation.constraints,List.ofFn_succ,Vector.getElem_zip,List.getElem?_cons_zero,List.cons_append,List.nil_append]
  have same := checked.1 _ (List.mem_of_getElem? first)
  exact sub_eq_zero.mp ((eval_sub ..).symm.trans same)

private theorem payload_lookups (r : Var Payload (ZMod p)) (m : Nat) : ((payloadMain r).operations m).lookups = [] := by
  simp [payloadMain,Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Gadgets.Equality.main,Operations.lookups,circuit_norm,List.ofFn_succ]

private theorem sum_lookups (r : Var AddressSum.Inputs (ZMod p)) (m : Nat) : ((AddressSum.main r).operations m).lookups = [] := by
  simp [AddressSum.main,WordRangeCheck.circuit,WordRangeCheck.main,Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Gadgets.Equality.main,Operations.lookups,circuit_norm]

private theorem word_lookups (r : Var Row (ZMod p)) (m : Nat) : ((wordMain r).operations m).lookups = [] := by
  simp [wordMain,payloadCircuit,AddressSum.circuit,payload_lookups,sum_lookups,Gadgets.Equality.main,Operations.lookups,circuit_norm,List.ofFn_succ]

/-- Padded word rows preserve each required channel's inactive semantics. -/
instance wordSupported : Guarded.Supported (wordCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    word_lookups
    (by
      intro ch mem
      have h : ch = cursorChannel.toRaw ∨ ch = blockChannel.toRaw ∨ ch = HostHintQueue.wordChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels,wordCircuit,wordElaborated,payloadCircuit,payloadElaborated,
          AddressSum.circuit,AddressSum.elaborated,circuit_norm,List.ofFn_succ,or_left_comm,or_comm,or_assoc] using mem
      rcases h with rfl|rfl|rfl <;> infer_instance)
    (by
      intro r m ch required outside i member
      simp only [wordCircuit,List.mem_cons,List.not_mem_nil,or_false] at required
      rcases required with rfl|rfl|rfl
      · exact False.elim (outside (by simp [wordCircuit,wordElaborated,circuit_norm]))
      · change i ∈ (((wordMain r).operations m).interactions.filter _) at member
        rw [word_ledger] at member
        simp [cursorChannel,blockChannel,HostHintQueue.wordChannel,circuit_norm] at member
        subst i
        rfl
      · exact False.elim (outside (by simp [wordCircuit,wordElaborated,circuit_norm])))

/-- One physical demand row per pointer and padded index. -/
def wordComponent : Component (ZMod p) where
  circuit := Guarded.circuit wordCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (wordCircuit (p := p)).name cursorChannel .push
    (fun c => [WriteBuffer.hintKey c.contents.pointer,WriteBuffer.hintKey c.index]) (fun r => r.1.prior) (fun r => r.2)
  Assumptions := (Guarded.circuit wordCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ h => h

omit [Fact (2^17 < p)] in
/-- A padded seed retains both sites in physical order. -/
theorem seed_channels :
    (seedComponent (p := p)).operations.interactions.map (·.channel) = [contentsChannel.toRaw,cursorChannel.toRaw] := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,seedComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  change (((seedMain _).operations _).interactions.map _).map _ = _
  rw [seed_ledger]
  rfl

/-- Physical channel inventory of a guarded word row. Both block occurrences survive padding. -/
theorem word_channels :
    (wordComponent (p := p)).operations.interactions.map (·.channel) =
      [cursorChannel.toRaw,blockChannel.toRaw,blockChannel.toRaw,HostHintQueue.wordChannel.toRaw,cursorChannel.toRaw] := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,wordComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  change (((wordMain _).operations _).interactions.map _).map _ = _
  rw [word_ledger]
  rfl

end SP1Clean.WriteAllocation.Words
