import SP1Clean.Proofs.Operations.WriteBuffer
import ToClean.Circuit.Guarded
import ToClean.Air.HintIndex
import Clean.Air.FlatComponent
import ToClean.Circuit.InteractionRecovery

/-! # Physical native WRITE buffer table family

Header demand creates one span. Positive cursor demand creates one word and its next cursor.
Clean's guard checks the entire selected input receipt. Both row types keep zero-weight padding.
-/

namespace SP1Clean.WriteBuffer
open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem no_general {I O : TypeMap} [ProvableType I] [ProvableType O]
    (c : GeneralFormalCircuit (ZMod p) I O) (target : RawChannel (ZMod p)) (outside : target ∉ c.channels)
    (args : Var I (ZMod p)) (n : ℕ) :
    ((FlatOperation.interactions (c.toSubcircuit n args).ops.toFlat).filter (fun i => decide (i.channel = target))) = [] := by
  rw [GeneralFormalCircuit.toSubcircuit_interactions]
  exact InteractionRecovery.interactionsWith_main_eq_nil c.base target args n outside

/-- The span arithmetic contributes only the existing Byte range requests. -/
theorem span_nonbyte (s : Var Span (ZMod p)) (offset : ℕ) (target : RawChannel (ZMod p))
    (other : target ≠ byteChannel.toRaw) :
    ((spanMain s).operations offset).interactionsWith target =
      [(WritePacket.channel.pulled s.header).toRaw, (channel.pushed s.source).toRaw, (channel.pulled s.target).toRaw,
       (effectHeaderChannel.pushed s.header).toRaw].filter
        (fun i => decide (i.channel = target)) := by
  have endpoint (roundUp : Bool) := no_general (Endpoint.circuit roundUp) target
    (by simpa [GeneralFormalCircuit.channels, Endpoint.circuit, Endpoint.elaborated, circuit_norm] using other)
  have range (args : Var Word (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil WordRangeCheck.circuit target args
      List.not_mem_nil List.not_mem_nil (n := n)
  have order (args : Var AddressOrder.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddressOrder.circuit target args
      List.not_mem_nil List.not_mem_nil (n := n)
  have sum (args : Var AddOperation.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddOperation.circuit target args
      (by simpa [AddOperation.circuit, circuit_norm] using other) List.not_mem_nil (n := n)
  simp only [spanMain, circuit_norm, List.nil_append]
  simp only [endpoint, range, order, sum, List.filter_cons, List.filter_nil, List.nil_append, circuit_norm]
  simp [FormalAssertion.toSubcircuit_interactions, circuit_norm, Operations.interactions]

/-- Every non-Byte word occurrence in actual circuit order. -/
theorem step_nonbyte (s : Var Step (ZMod p)) (offset : ℕ) (target : RawChannel (ZMod p))
    (other : target ≠ byteChannel.toRaw) :
    ((stepMain s).operations offset).interactionsWith target =
      [(channel.pulled s.source).toRaw, (WriteProbe.readChannel.pulled s.read).toRaw, (channel.pushed s.target).toRaw,
       (wordChannel.pushed s.read).toRaw].filter
        (fun i => decide (i.channel = target)) := by
  have division := no_general (AddressDiv8.circuit (p := p)) target (by simp [GeneralFormalCircuit.channels,
    AddressDiv8.circuit, AddressDiv8.elaborated, circuit_norm])
  have sum (args : Var AddrAddOperation.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddrAddOperation.circuit target args
      (by simpa [AddrAddOperation.circuit, circuit_norm] using other) List.not_mem_nil (n := n)
  simp only [stepMain, circuit_norm, List.nil_append]
  simp only [division, sum, List.filter_cons, List.filter_nil, List.nil_append, circuit_norm]
  simp [Gadgets.Equality.circuit, circuit_norm]

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
      have registered : selected = byteChannel.toRaw ∨ selected = WritePacket.channel.toRaw ∨ selected = channel.toRaw ∨ selected = effectHeaderChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, spanCircuit, spanElaborated, Endpoint.circuit, Endpoint.elaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro input offset selected required outside interaction present
      change selected ∈ [channel.toRaw, effectHeaderChannel.toRaw] at required
      rcases List.mem_cons.mp required with rfl | required
      · exact (outside (by simp [spanCircuit, spanElaborated, circuit_norm])).elim
      obtain rfl := List.mem_singleton.mp required
      change interaction ∈ ((spanMain input).operations offset).interactionsWith effectHeaderChannel.toRaw at present
      rw [span_nonbyte _ _ _ (by simp [effectHeaderChannel, byteChannel, circuit_norm])] at present
      simp [channel, WritePacket.channel, effectHeaderChannel, circuit_norm] at present
      subst interaction
      rfl)

instance stepGuardSupported : Guarded.Supported (stepCircuit (p := p)) :=
  Guarded.Supported.of_emitted_requirements _ step_lookups
    (by
      intro selected member
      have registered : selected = byteChannel.toRaw ∨ selected = channel.toRaw ∨ selected = WriteProbe.readChannel.toRaw ∨ selected = wordChannel.toRaw := by
        simpa [GeneralFormalCircuit.channels, stepCircuit, stepElaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl | rfl <;> infer_instance)
    (by
      intro input offset selected required outside interaction present
      change selected ∈ [channel.toRaw, wordChannel.toRaw] at required
      rcases List.mem_cons.mp required with rfl | required
      · exact (outside (by simp [stepCircuit, stepElaborated, circuit_norm])).elim
      obtain rfl := List.mem_singleton.mp required
      change interaction ∈ ((stepMain input).operations offset).interactionsWith wordChannel.toRaw at present
      rw [step_nonbyte _ _ _ (by simp [wordChannel, byteChannel, circuit_norm])] at present
      simp [channel, WriteProbe.readChannel, wordChannel, circuit_norm] at present
      subst interaction
      rfl)

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
