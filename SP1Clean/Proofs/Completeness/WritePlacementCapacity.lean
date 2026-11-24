import SP1Clean.Proofs.Operations.WriteDispatch
import SP1Clean.Proofs.Operations.WriteGroup
import SP1Clean.Native.Operations.WriteCursorBoundary
import SP1Clean.Proofs.Completeness.WriteProbeDemand
import SP1Clean.Proofs.Completeness.WriteStreamCapacity

/-! # Physical occurrence budgets for native WRITE effects

Count the whole ledger of each classifier, decoder, dispatcher, grouped word, fixed source
and terminal. The semantic demand estimate includes all released descriptors and both empty
and unaligned packets. All height formulas retain padded rows regardless of multiplicity.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics Machine FormalModel.Shard
open scoped Classical

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Entire native request row, including the empty physical classification interface. -/
theorem request_channels :
    (requestComponent (p := p)).operations.interactions.map (·.channel) =
      [WriteBuffer.effectHeaderChannel.toRaw,requestChannel.toRaw] := by
  have empty (x : Var Word (ZMod p)) (off : Nat) :
      FlatOperation.interactions (WriteDescriptor.circuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    apply WriteDescriptor.circuit.base.interactions_eq_nil_of_channels_eq_nil
    simp [FormalCircuitBase.channels,WriteDescriptor.circuit,WriteDescriptor.elaborated,circuit_norm]
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,requestComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  change (((requestMain _).operations _).interactions.map _).map _ = _
  simp only [requestMain,circuit_norm,empty,List.nil_append]
  rfl

/-- Every decoded word spends the four genuine paired-byte requests of the released decoder. -/
theorem word_channels :
    (wordComponent (p := p)).operations.interactions.map (·.channel) =
      [WriteBuffer.wordChannel.toRaw,Channels.byteChannel.toRaw,Channels.byteChannel.toRaw,
       Channels.byteChannel.toRaw,Channels.byteChannel.toRaw,octetsChannel.toRaw] := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,wordComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  simp only [wordCircuit,wordMain,FormalAssertion.toSubcircuit_interactions,U16toU8OperationSafe.circuit,
    U16toU8OperationSafe.main,circuit_norm]
  rfl

/-- Complete physical dispatcher row, including the four range checks on the raw SP1 pointer. -/
theorem dispatch_channels :
    (dispatchComponent (p := p)).operations.interactions.map (·.channel) =
      [requestChannel.toRaw,cursorChannel.toRaw,Channels.byteChannel.toRaw,Channels.byteChannel.toRaw,
       Channels.byteChannel.toRaw,Channels.byteChannel.toRaw,recordChannel.toRaw,recordChannel.toRaw,recordChannel.toRaw,
       queueEffectChannel.toRaw,positionChannel.toRaw,positionChannel.toRaw,cursorChannel.toRaw] := by
  have sum (x : Var AddressSum.Inputs (ZMod p)) (off : Nat) :
      FlatOperation.interactions (AddressSum.circuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    exact AddressSum.interactions x off
  have noRange (x : Var Word (ZMod p)) (off : Nat) :
      ((WordRangeCheck.circuit.main x).operations off).interactions = [] := by
    apply WordRangeCheck.circuit.base.interactions_eq_nil_of_channels_eq_nil
    rfl
  have flags (x : Expression (ZMod p)) (off : Nat) :
      FlatOperation.interactions (flagsCircuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [GeneralFormalCircuit.toSubcircuit_interactions]
    apply flagsCircuit.base.interactions_eq_nil_of_channels_eq_nil
    simp [FormalCircuitBase.channels,flagsCircuit,flagsElaborated,circuit_norm]
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,dispatchComponent,Guarded.circuit]
  rw [Guarded.main_interactions]
  change (((dispatchMain _).operations _).interactions.map _).map _ = _
  simp only [dispatchMain,circuit_norm,sum,flags,List.nil_append]
  simp only [FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.circuit,Gadgets.Equality.main,WriteStart.circuit,WriteStart.main,
    noRange,AddOperation.circuit,AddOperation.main,circuit_norm,List.nil_append,List.append_nil]
  rfl

/-- The sources each own one physical occurrence per row; the close row and verifier own two. -/
theorem boundary_channels (source target : ExecutionSnapshot) :
    (streamComponent (p := p) source.host target.host).operations.interactions.map (·.channel) = [recordChannel.toRaw] ∧
    (blockComponent (p := p) source.host target.host).operations.interactions.map (·.channel) = [blockChannel.toRaw] ∧
    (planComponent (p := p)).operations.interactions.map (·.channel) = [sliceChannel.toRaw] ∧
    (closeComponent (p := p) source target).operations.interactions.map (·.channel) = [cursorChannel.toRaw,closeChannel.toRaw] ∧
    (cursorEndpoint (p := p) source target).operations.interactions.map (·.channel) = [cursorChannel.toRaw,closeChannel.toRaw] := by
  have source_channels {Row : TypeMap} [ProvableType Row] (s : StaticTable (ZMod p) Row) (target : Channel (ZMod p) Row)
      (valid : ∀ row, s.Spec row → ∀ data, target.Guarantees row data) (bound : s.height < UInt64.size) :
      (s.payloadComponent target valid bound).operations.interactions.map (·.channel) = [target.toRaw] := by
    rw [Component.interactions_eq]
    simp only [Component.rowOperations,StaticTable.payloadComponent,StaticTable.payloadProvider,circuit_norm]
  refine ⟨source_channels ..,source_channels ..,source_channels ..,?_,rfl⟩
  have sum (x : Var AddressSum.Inputs (ZMod p)) (off : Nat) :
      FlatOperation.interactions (AddressSum.circuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    exact AddressSum.interactions x off
  rw [Component.interactions_eq]
  simp only [Component.rowOperations,closeComponent,closeCircuit,closeMain,circuit_norm,sum,List.nil_append]

/-- Count any channel across all eight physical effect tables and their verifier. Take the
actual heights of the tables, including padding. Each term is one named share of the joint
inventory, so other assembly components can add their own shares on the same channels. -/
theorem placement_occurrences (source target : ExecutionSnapshot)
    (header word dispatch group metadata blocks plans terminal : Table (ZMod p))
    (hh : header.component = requestComponent) (hw : word.component = wordComponent)
    (hd : dispatch.component = dispatchComponent) (hg : group.component = groupComponent)
    (hm : metadata.component = streamComponent source.host target.host)
    (hb : blocks.component = blockComponent source.host target.host) (hp : plans.component = planComponent)
    (ht : terminal.component = closeComponent source target) (ch : RawChannel (ZMod p)) :
    let hit := fun (k : RawChannel (ZMod p)) => if k = ch then 1 else 0
    ((cursorEndpoint source target).operations.interactionsWith ch).length +
        ([header,word,dispatch,group,metadata,blocks,plans,terminal].flatMap (·.interactionsWith ch)).length =
      hit WriteBuffer.effectHeaderChannel.toRaw * header.length +
      hit requestChannel.toRaw * (header.length + dispatch.length) +
      hit WriteBuffer.wordChannel.toRaw * word.length +
      hit octetsChannel.toRaw * (word.length + group.length) +
      hit sliceChannel.toRaw * (plans.length + group.length) +
      hit positionChannel.toRaw * (2 * dispatch.length + 2 * group.length) +
      hit blockChannel.toRaw * (blocks.length + 2 * group.length) +
      hit recordChannel.toRaw * (metadata.length + 3 * dispatch.length) +
      hit queueEffectChannel.toRaw * dispatch.length +
      hit cursorChannel.toRaw * (1 + terminal.length + 2 * dispatch.length) +
      hit closeChannel.toRaw * (1 + terminal.length) +
      hit Channels.byteChannel.toRaw * (4 * word.length + 4 * dispatch.length) := by
  dsimp only
  have width (ops : Operations (ZMod p)) :
      (ops.interactionsWith ch).length = (ops.interactions.map (·.channel)).countP (fun k => decide (k = ch)) := by
    rw [List.countP_map, List.countP_eq_length_filter]
    rfl
  obtain ⟨metadataBound,block,plan,close,verifier⟩ := boundary_channels (p := p) source target
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,Table.interactionsWith_length,
    hh,hw,hd,hg,hm,hb,hp,ht,Component.channelWidth,width,request_channels,word_channels,dispatch_channels,group_channels,
    metadataBound,block,plan,close,verifier,List.countP_cons,List.countP_nil,decide_eq_true_eq]
  ring

/-- The actual demand-mode scheduler rounds classifier, decoder, dispatcher and grouped word
rows by the same rule. Missing demand contributes zero. -/
theorem placement_targetHeight (state : WitnessGeneration.ComponentState (ZMod p))
    (installed : state.component = requestComponent ∨ state.component = wordComponent ∨
      state.component = dispatchComponent ∨ state.component = groupComponent) :
    state.targetHeight = WitnessGeneration.demandHeight state.rows.size := by
  cases state with
  | mk component multiplicity operations interactions rows messageRows =>
    rcases installed with eq | eq | eq | eq <;> change component = _ at eq <;> subst component <;>
      exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl

/-- The actual resource preset pays for both demand table heights from the recovered event tape. -/
theorem admissible_placement_heights {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE (.native SP1Prime)) :
    ∃ packets, TraceGen.WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      packets.length = events.countP TraceGen.WriteObservations.isWriteCall ∧
      WitnessGeneration.demandHeight packets.length ≤ 2^16 ∧
      WitnessGeneration.demandHeight (TraceGen.WriteObservations.wordProbes packets) ≤ 2^28 := by
  obtain ⟨packets, collected⟩ := TraceGen.WriteObservations.admissible_packets run
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have reads := run.2.2.1 .readBytes
  obtain ⟨calls, words, _, _⟩ := TraceGen.WriteObservations.packets_native_bound run.1.2 collected
    (ticks.trans preset.2.1) (reads.trans preset.2.2.1)
  exact ⟨packets,collected,TraceGen.WriteObservations.packets_length collected,
    WitnessGeneration.demandHeight_le_pow (by omega),WitnessGeneration.demandHeight_le_pow (by omega)⟩

end SP1Clean.WriteEffects
