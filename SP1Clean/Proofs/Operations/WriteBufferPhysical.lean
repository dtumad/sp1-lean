import SP1Clean.Proofs.Operations.WriteBuffer
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import Clean.Air.FlatComponent

/-! # Physical native WRITE buffer table family

Header demand creates one span. Positive cursor demand creates one word and its next cursor.
Clean's guard checks the entire selected input receipt. Both row types keep zero-weight padding.
-/

namespace SP1Clean.WriteBuffer
open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem span_lookups (input : Var Span (ZMod p)) (offset : ℕ) :
    ((spanMain input).operations offset).lookups = [] := by
  simp [spanMain, Endpoint.circuit, circuit_norm, Endpoint.main,
    WordRangeCheck.circuit, WordRangeCheck.main, AddressOrder.circuit, AddressOrder.main,
    AddOperation.circuit, AddOperation.main, AddressDiv8.circuit, AddressDiv8.main,
    AddrAddOperation.circuit, AddrAddOperation.main, Gadgets.IsZeroField.circuit, Gadgets.Equality.main,
    Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Operations.lookups]

private theorem step_lookups (input : Var Step (ZMod p)) (offset : ℕ) :
    ((stepMain input).operations offset).lookups = [] := by
  simp [stepMain, circuit_norm, AddressDiv8.circuit, AddressDiv8.main, AddrAddOperation.circuit,
    AddrAddOperation.main, Gadgets.Equality.main, Gadgets.ToBits.rangeCheck,
    Gadgets.ToBits.toBits, Gadgets.ToBits.main, Operations.lookups]

instance spanGuardSupported : Guarded.Supported (spanCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ span_lookups
    (by
      intro selected member
      change selected ∈ _ ++ [channel.toRaw] at member
      have registered : selected = byteChannel.toRaw ∨ selected = WritePacket.channel.toRaw ∨ selected = channel.toRaw := by
        simpa [spanCircuit, spanElaborated, Endpoint.circuit, Endpoint.elaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl <;> infer_instance)
    (by
      intro _ _ selected required outside _ _
      obtain rfl := List.mem_singleton.mp required
      exact (outside (by simp [spanCircuit, spanElaborated, circuit_norm])).elim)

instance stepGuardSupported : Guarded.Supported (stepCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ step_lookups
    (by
      intro selected member
      have registered : selected = byteChannel.toRaw ∨ selected = channel.toRaw ∨ selected = WriteProbe.readChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, stepCircuit, stepElaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl <;> infer_instance)
    (by
      intro _ _ selected required outside _ _
      obtain rfl := List.mem_singleton.mp required
      exact (outside (by simp [stepCircuit, stepElaborated, circuit_norm])).elim)

/-- Guarded table row with an explicit physical activity. -/
abbrev SpanRow := ProvablePair Span field
/-- Guarded one-word row with an explicit physical activity. -/
abbrev WordRow := ProvablePair Step field

/-- The installed packet domain uses full absolute clocks and full cell indices as hint keys. -/
def hintKey {F : Type} [FiniteField F] (limbs : fields 3 (Expression F)) : Witgen.U64Expr F :=
  limbs[0].val + limbs[1].val * 65536 + limbs[2].val * 4294967296

/-- Span rows answer the exact original WRITE packet. -/
def spanComponent : Component (ZMod p) where
  circuit := Guarded.circuit spanCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (spanCircuit (p := p)).name WritePacket.channel .push
    (fun h => [hintKey h.clock]) (fun s => s.1.header) (fun s => s.2)
  Assumptions := (Guarded.circuit spanCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

/-- Each unanswered source cursor produces exactly one aligned-word observation row. -/
def wordComponent : Component (ZMod p) where
  circuit := Guarded.circuit stepCircuit inferInstance
  generation := Witgen.HintIndex.unitDemandKeys (stepCircuit (p := p)).name channel .push
    (fun c => [hintKey c.clock, hintKey c.index]) (fun s => s.1.source) (fun s => s.2)
  Assumptions := (Guarded.circuit stepCircuit inferInstance).Assumptions
  circuit_assumptions_of_assumptions := fun _ _ _ _ _ assumed => assumed

/-- Native buffer ownership slots in span-then-word order. -/
def components : List (Component (ZMod p)) := [spanComponent, wordComponent]

end SP1Clean.WriteBuffer
