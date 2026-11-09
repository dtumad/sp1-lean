import ToClean.Gadgets.Equality
import SP1Clean.Native.Chips.HostHintReadChip.Defs

/-! # Soundness and completeness of HINT_READ coordination

The handler's semantic contract relates the complete call and queue transition to the exact
padded endpoints. The span constructor supplies its quotient columns; all other completeness
conditions are semantic. Node and final-word contents still need ledger authentication.
-/

namespace SP1Clean.HostHintReadChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  HintReadSpan.ProverAssumptions input.span ∧ Spec input

omit [Fact (2 ^ 25 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (address : fields 3 (Expression (ZMod p))) :
    Eval.eval env (Address.asWord address) =
      Address.asWord (Eval.eval env address) := by
  simp only [Address.asWord, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_endStep (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env input.endStep = (ProvableStruct.eval env input).endStep := by
  rcases input with ⟨call, previous, node, span, lastIndex, lastValue⟩
  rcases node with ⟨pointer, tail, length⟩
  rcases span with ⟨start, quotients, length, last, count⟩
  simp only [Inputs.endStep, circuit_norm]

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  computableWitnesses := by
    intro n input env env'
    constructor
    · simp only [main, circuit_norm, Nat.add_zero,
        Gadgets.Equality.toSubcircuit_computableWitnesses]
      repeat' apply And.intro
      all_goals intro h
      all_goals first
        | exact Subcircuit.computableWitnesses_of_localLength_zero _ _ _ _ rfl
        | apply GeneralFormalCircuit.toSubcircuit_computableWitnesses _ rfl
          intro _
          simp only [circuit_norm, Inputs.clock, Inputs.endStep, h]
    · intro _ _
      rfl
  name := "sp1.native.hint_read"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  channelsWithRequirements := [HostHintQueue.nodeChannel.toRaw, HostHintQueue.wordChannel.toRaw,
    HostCallChip.channel.toRaw, HostHintQueue.stateChannel.toRaw, HintReadWordChip.stateChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, HintReadSpan.circuit,
      HintReadStep.circuit, HostHintQueue.nodeChannel, HostCallChip.channel, HostHintQueue.stateChannel,
      HintReadWordChip.stateChannel, Inputs.clock, Inputs.next, Inputs.first, Inputs.final,
      Vector.map_id', eval_asWord, eval_endStep]
    simpa only [h_input] using h_holds
  completeness := by
    circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit, HintReadSpan.circuit,
      HintReadStep.circuit, HostHintQueue.nodeChannel, HostCallChip.channel, HostHintQueue.stateChannel,
      HintReadWordChip.stateChannel, Inputs.clock, Inputs.next, Inputs.first, Inputs.final,
      Vector.map_id', eval_asWord, eval_endStep]
    obtain ⟨span, valid⟩ := h_assumptions
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1,
      valid.2.2.2.2.2.1, valid.2.2.2.2.2.2.1, valid.2.2.2.2.2.2.2.1, span,
      valid.2.2.2.2.2.2.2.2.2.1, valid.2.2.2.2.2.2.2.2.2.2⟩
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm, ClockOrder.circuit, HintReadSpan.circuit,
        HintReadStep.circuit, Gadgets.Equality.circuit]
    · simp only [main, circuit_norm, ClockOrder.circuit, HintReadSpan.circuit,
        HintReadStep.circuit, Gadgets.Equality.circuit]
      tauto
    · intro env _
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction member
      apply Or.inl
      have selected := List.mem_map_of_mem (f := fun item : AbstractInteraction (ZMod p) => item.channel) member
      rw [← Operations.shallowChannels_eq_interactions_map] at selected
      simp only [main, circuit_norm] at selected ⊢
      tauto

end SP1Clean.HostHintReadChip
