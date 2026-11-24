import SP1Clean.Export.WriteObservationByte
import ToClean.Air.Footprint

/-! # Physical Byte reads in the nineteen native observation tables -/

namespace SP1Clean.Export.WriteObservationAssembly

open Air.Flat Circuit Semantics Channels
private abbrev F := ZMod SP1Prime

private def profile (c : Component F) (width : Nat) : Bool :=
  let name := (byteChannel (p := SP1Prime)).name
  (c.operations.interactions.all fun i => i.channel.name != name || i.direction == .pull) &&
    (c.operations.interactions.countP (·.channel.name == name) == width)

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

local macro "check_observer_profile" c:ident : tactic => `(tactic| (
  rw [profile, Component.interactions_eq, Component.rowOperations]
  unfold $c
  simp only [Guarded.circuit, Guarded.main_interactions, List.all_map, List.countP_map]
  simp only [circuit_norm]
  first | rfl | decide +kernel))

private theorem span_profile : profile WriteBuffer.spanComponent 10 = true := by check_observer_profile WriteBuffer.spanComponent
private theorem word_profile : profile WriteBuffer.wordComponent 3 = true := by check_observer_profile WriteBuffer.wordComponent
private theorem octet_profile : profile WriteEffects.wordComponent 4 = true := by check_observer_profile WriteEffects.wordComponent
private theorem dispatch_profile : profile WriteEffects.dispatchComponent 4 = true := by check_observer_profile WriteEffects.dispatchComponent
private theorem allocation_profile : profile WriteAllocation.stepComponent 3 = true := by check_observer_profile WriteAllocation.stepComponent

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
  have measured : ∃ width, profile c width = true := by
    rcases found with h | h | h | h | h <;> rw [h]
    · exact ⟨_,span_profile⟩
    · exact ⟨_,word_profile⟩
    · exact ⟨_,octet_profile⟩
    · exact ⟨_,dispatch_profile⟩
    · exact ⟨_,allocation_profile⟩
  obtain ⟨_, checked⟩ := measured
  have pulls := ((Bool.and_eq_true ..).mp checked).1
  simpa only [onByte, Channel.toRaw_name, bne_self_eq_false, Bool.false_or, beq_iff_eq] using
    List.all_eq_true.mp pulls i raw

/-- Widths in physical observer order. Each width is charged on every padded row. -/
def observerByteWidths : List Nat := [0,0,0,10,3,0,4,0,4,0,0,0,0,0,0,0,3,0,0]

private def byteSites (c : Component F) : Nat :=
  c.operations.interactions.countP (·.channel.name == (byteChannel (p := SP1Prime)).name)

private theorem silent_width (c : Component F)
    (absent : (byteChannel (p := SP1Prime)).name ∉ c.circuit.channels.map RawChannel.name) : byteSites c = 0 := by
  unfold byteSites
  rw [List.countP_eq_length_filter]
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro a seen same
  apply absent
  rw [← beq_iff_eq.mp same]
  apply List.mem_map_of_mem
  apply c.circuit.channels_subset c.rowInputVar c.rowOffset
  exact List.mem_map_of_mem (c.interactions_eq ▸ seen)

private theorem checked_width {c : Component F} {width : Nat} (checked : profile c width = true) :
    byteSites c = width := beq_iff_eq.mp (((Bool.and_eq_true ..).mp checked).2)

attribute [local irreducible] byteSites preprocessing

private theorem observer_site_widths (source target : ExecutionSnapshot) :
    (tables source target).map byteSites = observerByteWidths := by
  simp only [tables, observerByteWidths, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals try exact silent_width _ (of_decide_eq_true rfl)
  · exact checked_width span_profile
  · exact checked_width word_profile
  · exact checked_width octet_profile
  · exact checked_width dispatch_profile
  · exact checked_width allocation_profile

/-- The typed widths used by the native Byte balance agree with the five measured circuits
and vanish on the other fourteen observer slots. -/
theorem observer_byte_widths (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F) :
    (tables source target).map (·.channelWidth byteChannel.toRaw) = observerByteWidths := by
  let ens := preprocessing image source target final
  have listed {c : Component F} (member : c ∈ tables source target) : c ∈ ens.tables := by
    dsimp only [ens]
    rw [(appended image source target final).tables]
    exact List.mem_append_right _ member
  have span : WriteBuffer.spanComponent ∈ tables source target :=
    List.getElem_mem (l := tables source target) (n := 3) (by change 3 < 19; decide)
  have registered : byteChannel.toRaw ∈ ens.channels := ens.tables_channels _ (listed span)
    (show byteChannel.toRaw ∈ WriteBuffer.spanComponent.circuit.channels from List.mem_cons_self)
  rw [← observer_site_widths source target]
  apply List.map_congr_left
  intro c member
  unfold byteSites
  exact ens.channelWidth_eq_countP (listed member) registered

private theorem physical_count (rows : List (Table F)) (ch : RawChannel F) :
    (rows.flatMap (·.interactionsWith ch)).length =
      (List.zipWith (· * ·) (rows.map Table.length) (rows.map (·.component.channelWidth ch))).sum := by
  induction rows with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.flatMap_cons, List.length_append, Table.interactionsWith_length, List.map_cons,
      List.zipWith_cons_cons, List.sum_cons, ih]

/-- The ordered generated suffix pays exactly its padded heights times the measured
Byte widths, before any canonical data rebind. -/
theorem generated_byte_count (image : ProgramImage) {source target : ExecutionSnapshot} (final : HostHintQueue.State F)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target) :
    (suffix.flatMap (·.interactionsWith byteChannel.toRaw)).length =
      (List.zipWith (· * ·) (suffix.map Table.length) observerByteWidths).sum := by
  rw [physical_count, ← observer_byte_widths image source target final, ← registered, List.map_map]
  rfl

/-- The complete observer Byte ledger charges its actual five circuits at their actual padded
heights. The other fourteen slots spend no Byte sites, regardless of their height. -/
theorem observer_byte_count {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
    (w : EnsembleWitness (assembly image source target final)) :
    ((w.tables.drop 98).flatMap (·.interactionsWith byteChannel.toRaw)).length =
      (List.zipWith (· * ·) (w.heights.drop 98) observerByteWidths).sum := by
  have original : (WriteSourceRegistry.withSources image source target final).tables.length = 98 := by
    rw [WriteSourceRegistry.tables_eq, List.length_mapIdx, WriteSourceRegistry.base_length]
  have layout : (assembly image source target final).tables =
      (WriteSourceRegistry.withSources image source target final).tables ++ tables source target :=
    (appended image source target final).tables
  have registered : (w.tables.drop 98).map Table.component = tables source target := by
    rw [List.map_drop, w.tables_map_component, layout, ← original, List.drop_left]
  rw [generated_byte_count image final _ registered, List.map_drop]
  rfl

end SP1Clean.Export.WriteObservationAssembly
