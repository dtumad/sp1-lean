import SP1Clean.Proofs.Chips.WritePacket.Formal
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import Clean.Air.FlatComponent

/-! # Native WRITE packet table and its physical occurrences -/

namespace SP1Clean.WritePacket

open Circuit Air.Flat

variable {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Complete active handoff at the physical row, in emission order. -/
theorem main_interactions (input : Var Inputs (ZMod p)) (offset : Nat) :
    ((main input).operations offset).interactions =
      [(HostCallChip.channel.pulled input.call).toRaw, (WriteProbe.readChannel.pulled input.read).toRaw,
        (channel.pushed input.header).toRaw] := by
  simp [main, ClockParts.circuit, ClockParts.main, circuit_norm, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Gadgets.Equality.main,
    Operations.interactions, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions]

instance guardSupported : Guarded.Supported (circuit (p := p)) where
  noLookups := by
    intro input offset
    simp [circuit, main, ClockParts.circuit, ClockParts.main, circuit_norm, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Gadgets.Equality.main,
      Operations.lookups]
  channelsNeutral := by
    intro ch member
    change ch ∈ [HostCallChip.channel.toRaw, WriteProbe.readChannel.toRaw, (channel (p := p)).toRaw] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> infer_instance
  declared := by
    intro input offset interaction member pulls
    rw [GeneralFormalCircuit.toSubcircuit_interactions] at member
    change interaction ∈ ((main input).operations offset).interactions at member
    rw [main_interactions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · contradiction

/-- Demand-padded WRITE rows share one activity bit for both reads and the packet output. -/
def guarded : GeneralFormalCircuit (ZMod p) (ProvablePair Inputs field) unit :=
  Guarded.circuit circuit guardSupported

/-- The private index routes by the incoming 48-bit ECALL clock. Clean demands equality of the
entire instruction handoff, including code, both arguments and return. -/
def component : Component (ZMod p) where
  circuit := guarded
  generation := Witgen.HintIndex.unitDemand (guarded (p := p)).name HostCallChip.channel .push
    (fun call => call.clk_high.val * 16777216 + call.clk_low.val)
    (fun input => input.1.call) (fun input => input.2)
  Assumptions := guarded.Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

end SP1Clean.WritePacket
