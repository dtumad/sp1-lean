import SP1Clean.Native.Operations.OrdinaryObservation
import ToClean.Circuit.Guarded

/-! # Padding the ordinary observation consumer

Each live row consumes an instruction receipt. The additional activity field makes physical
padding inert on every channel while retaining the original number of occurrences.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The last input cell controls all receipt, observation and Byte interactions. -/
abbrev RowInput := ProvablePair Inputs field

/-- Supply a populated observation as a live consumer row. -/
def activeRow (input : Inputs (ZMod p)) : RowInput (ZMod p) := (input, 1)

/-- Every pulled channel can discharge its declared guarantee at zero multiplicity. -/
instance guardSupported : Guarded.Supported (circuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (fun _ _ => by
      simp [circuit, main, ClockOrder.circuit, ClockOrder.main, Gadgets.ToBits.rangeCheck,
        Gadgets.toBits, Gadgets.Equality.main, Gadgets.IsZeroField.circuit, WordRangeCheck.circuit, AddOperation.circuit,
        AddOperation.main, assertBool, circuit_norm])
    (by
      intro channel member
      have included := circuit_channels_subset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl <;> infer_instance)
    (by
      intro _ _ channel required outside
      exfalso
      apply outside
      have guarantees : (circuit (p := p)).channelsWithGuarantees =
          [byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
            InstructionReceipt.channel.toRaw, stateChannel.toRaw] := rfl
      rw [guarantees]
      exact List.mem_append_right [_, _, _, _] required)

/-- Disable every child constraint and interaction on a Boolean padding row. -/
def guardedCircuit : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit circuit guardSupported

end SP1Clean.OrdinaryObservation
