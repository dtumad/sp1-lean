import SP1Clean.Proofs.Completeness.WriteBufferAssembly
import ToClean.Air.Footprint

/-! # Exact physical channel costs of the mixed WRITE buffer block -/

namespace SP1Clean.WriteBuffer

open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The complete circuit channel sequence of a padded span row. -/
theorem span_channels : ((spanComponent (p := p)).operations.interactions.map (·.channel)) =
    List.replicate 10 byteChannel.toRaw ++ [WritePacket.channel.toRaw, channel.toRaw, channel.toRaw, effectHeaderChannel.toRaw] := by
  rw [Component.interactions_eq]
  change (((Guarded.main spanCircuit spanGuardSupported (varFromOffset SpanRow 0)).operations (size SpanRow)).interactions.map (·.channel)) = _
  rw [Guarded.main_interactions, List.map_map]
  simp only [spanCircuit, spanMain, FormalCircuit.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    Endpoint.circuit, Endpoint.main, AddrAddOperation.circuit, AddrAddOperation.main, AddOperation.circuit, AddOperation.main,
    WordRangeCheck.circuit, WordRangeCheck.main, AddressOrder.circuit, AddressOrder.main, AddressDiv8.circuit, AddressDiv8.main,
    Gadgets.IsZeroField.circuit, Gadgets.Equality.circuit, Gadgets.Equality.main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main,
    List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero, circuit_norm]
  rfl

/-- The complete circuit channel sequence of a padded aligned-word row. -/
theorem word_channels : ((wordComponent (p := p)).operations.interactions.map (·.channel)) =
    List.replicate 3 byteChannel.toRaw ++ [channel.toRaw, WriteProbe.readChannel.toRaw, channel.toRaw, wordChannel.toRaw] := by
  rw [Component.interactions_eq]
  change (((Guarded.main stepCircuit stepGuardSupported (varFromOffset WordRow 0)).operations (size WordRow)).interactions.map (·.channel)) = _
  rw [Guarded.main_interactions, List.map_map]
  simp only [stepCircuit, stepMain, GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    AddressDiv8.circuit, AddressDiv8.main, AddrAddOperation.circuit, AddrAddOperation.main,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main,
    List.map_cons, List.map_nil, List.nil_append, List.append_nil, List.ofFn_succ, List.ofFn_zero, circuit_norm]
  rfl

/-- All signed occurrences at the two native heights; this applies to any channel,
including those with no occurrence in either physical circuit. -/
theorem channel_cost (spans : List (Span (ZMod p))) (words : List (Step (ZMod p))) (data : ProverData (ZMod p))
    (hs hw) (ch : RawChannel (ZMod p)) :
    let sp := spanTable spans data hs
    let wd := wordTable words data hw
    (sp.interactionsWith ch ++ wd.interactionsWith ch).length =
      WitnessGeneration.demandHeight spans.length * ((List.replicate 10 byteChannel.toRaw ++
        [WritePacket.channel.toRaw, channel.toRaw, channel.toRaw, effectHeaderChannel.toRaw]).countP (fun item => decide (item = ch))) +
      WitnessGeneration.demandHeight words.length * ((List.replicate 3 byteChannel.toRaw ++
        [channel.toRaw, WriteProbe.readChannel.toRaw, channel.toRaw, wordChannel.toRaw]).countP (fun item => decide (item = ch))) := by
  have width (c : Component (ZMod p)) : c.channelWidth ch = (c.operations.interactions.map (·.channel)).countP (fun item => decide (item = ch)) := by
    rw [List.countP_map, List.countP_eq_length_filter]
    rfl
  let sp := spanTable spans data hs
  let wd := wordTable words data hw
  have sh : sp.length = WitnessGeneration.demandHeight spans.length := spanTable_length _ _ _
  have wh : wd.length = WitnessGeneration.demandHeight words.length := wordTable_length _ _ _
  change (sp.interactionsWith ch ++ wd.interactionsWith ch).length = _
  rw [List.length_append, Table.interactionsWith_length, Table.interactionsWith_length, sh, wh,
    show sp.component = spanComponent by rfl, show wd.component = wordComponent by rfl, width, width, span_channels, word_channels]

end SP1Clean.WriteBuffer
