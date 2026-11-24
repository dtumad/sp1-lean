import SP1Clean.Export.WriteObservationByte

/-! # Physical Byte reads in the nineteen native observation tables -/

namespace SP1Clean.Export.WriteObservationAssembly

open Air.Flat Circuit Semantics Channels
private abbrev F := ZMod SP1Prime

private def pullSites (c : Component F) : Bool :=
  c.operations.interactions.all fun i => i.channel.name != (byteChannel (p := SP1Prime)).name || i.direction == .pull

attribute [local circuit_norm] GeneralFormalCircuit.toSubcircuit_interactions FormalCircuit.toSubcircuit_interactions
  FormalAssertion.toSubcircuit_interactions WriteBuffer.spanCircuit WriteBuffer.spanMain WriteBuffer.stepCircuit WriteBuffer.stepMain
  WriteEffects.wordCircuit WriteEffects.wordMain WriteEffects.dispatchCircuit WriteEffects.dispatchMain
  WriteAllocation.stepCircuit WriteAllocation.stepMain WriteBuffer.Endpoint.circuit WriteBuffer.Endpoint.main
  AddressDiv8.circuit AddressDiv8.main AddressOrder.circuit AddressOrder.main AddressSum.circuit AddressSum.main
  AddrAddOperation.circuit AddrAddOperation.main AddOperation.circuit AddOperation.main
  HintNodeAllocate.circuit HintNodeAllocate.main WriteStart.circuit WriteStart.main WriteEffects.flagsCircuit WriteEffects.flagsMain
  U16toU8OperationSafe.circuit U16toU8OperationSafe.main WordRangeCheck.circuit WordRangeCheck.main
  Gadgets.Equality.circuit Gadgets.Equality.main Gadgets.IsZeroField.circuit Gadgets.ToBits.rangeCheck
  Gadgets.toBits Gadgets.ToBits.main

local macro "check_observer_pulls" c:ident : tactic => `(tactic| (
  rw [pullSites, Component.interactions_eq, Component.rowOperations]
  unfold $c
  simp only [Guarded.circuit, Guarded.main_interactions, List.all_map]
  simp only [circuit_norm]
  first | rfl | decide +kernel))

private theorem span_pulls : pullSites WriteBuffer.spanComponent = true := by check_observer_pulls WriteBuffer.spanComponent
private theorem word_pulls : pullSites WriteBuffer.wordComponent = true := by check_observer_pulls WriteBuffer.wordComponent
private theorem octet_pulls : pullSites WriteEffects.wordComponent = true := by check_observer_pulls WriteEffects.wordComponent
private theorem dispatch_pulls : pullSites WriteEffects.dispatchComponent = true := by check_observer_pulls WriteEffects.dispatchComponent
private theorem allocation_pulls : pullSites WriteAllocation.stepComponent = true := by check_observer_pulls WriteAllocation.stepComponent

/-- The five physical circuits that interact with Byte use it only as a reader. -/
theorem observer_byte_direction {source target : ExecutionSnapshot} (c : Component F)
    (installed : c ∈ tables source target) (i : AbstractInteraction F)
    (emitted : i ∈ c.operations.interactionsWith byteChannel.toRaw) : i.direction = .pull := by
  have onByte := Operations.channel_eq_of_mem_interactionsWith emitted
  have raw : i ∈ c.operations.interactions := List.mem_of_mem_filter emitted
  have used : byteChannel.toRaw ∈ c.circuit.channels := by
    apply c.circuit.channels_subset c.rowInputVar c.rowOffset
    exact List.mem_map.mpr ⟨i, c.interactions_eq ▸ raw, onByte⟩
  let hasByte (c : Component F) := (c.circuit.channels.map RawChannel.name).contains (byteChannel (p := SP1Prime)).name
  have readers : (tables source target).filter hasByte = [WriteBuffer.spanComponent, WriteBuffer.wordComponent,
      WriteEffects.wordComponent, WriteEffects.dispatchComponent, WriteAllocation.stepComponent] := rfl
  have found : c ∈ (tables source target).filter hasByte :=
    List.mem_filter.mpr ⟨installed, List.contains_iff_mem.mpr (List.mem_map_of_mem used)⟩
  rw [readers] at found
  simp only [List.mem_cons, List.not_mem_nil, or_false] at found
  have pulls : pullSites c = true := by
    rcases found with h | h | h | h | h <;> rw [h]
    · exact span_pulls
    · exact word_pulls
    · exact octet_pulls
    · exact dispatch_pulls
    · exact allocation_pulls
  simpa only [onByte, Channel.toRaw_name, bne_self_eq_false, Bool.false_or, beq_iff_eq] using
    List.all_eq_true.mp pulls i raw

end SP1Clean.Export.WriteObservationAssembly
