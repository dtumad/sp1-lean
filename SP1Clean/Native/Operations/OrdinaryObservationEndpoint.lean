import SP1Clean.Native.Operations.OrdinaryObservationBoundary
import ToClean.Air.VerifierExtension

/-! # Verifier-owned ordinary observation endpoints

The supplied source and target fix both ends of the observation chain: the source's retirement
counter and nextPC at clock zero, and the target's at the terminal's sentinel clock. This
zero-input closed circuit pushes the first and pulls the second, so its ledger is exactly those two
occurrences. It allocates no assertion channel; it joins the verifier through
`ClosedVerifier.withInteractions`.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Air.Flat
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Push the chain's start and pull its final link. -/
def endpointMain (initial outgoing : State (ZMod p)) (_ : Var unit (ZMod p)) :
    Circuit (ZMod p) Unit := do
  stateChannel.push (const initial)
  stateChannel.pull (const outgoing)

/-- The endpoint circuit, with no witness and no assertion. -/
def endpointCircuit (initial outgoing : State (ZMod p)) : GeneralFormalCircuit (ZMod p) unit unit where
  main := endpointMain initial outgoing
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by circuit_proof_start [endpointMain, stateChannel]
  completeness := by circuit_proof_start [endpointMain, stateChannel]

/-- The endpoint emits one push and one pull on the observation channel. -/
theorem endpoint_interactions (initial outgoing : State (ZMod p)) (offset : ℕ) :
    ((endpointMain initial outgoing ()).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pushed (const initial)).toRaw, (stateChannel.pulled (const outgoing)).toRaw] := by
  simp only [endpointMain, circuit_norm]

/-- The endpoint ledger is exactly the start push and the final pull. -/
theorem endpoint_values (initial outgoing : State (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (channel : RawChannel (ZMod p)) :
    ((endpointMain initial outgoing ()).operations offset).interactionValuesWith channel env =
      if channel = stateChannel.toRaw then
        [stateChannel.pushedValue initial, stateChannel.pulledValue outgoing] else [] := by
  by_cases same : channel = stateChannel.toRaw
  · subst channel
    simp only [Operations.interactionValuesWith, endpoint_interactions, List.map_cons, List.map_nil,
      Channel.eval_pulled, Channel.eval_pushed, ProvableType.eval_const, ↓reduceIte]
  · simp only [endpointMain, Operations.interactionValuesWith, Operations.interactionsWith,
      circuit_norm, ChannelInteraction.toRaw, List.filter_cons, List.filter_nil, Ne.symm same,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.map_nil, ite_eq_right same]

/-- The closed endpoint verifier for a supplied source and target. -/
def endpoint (initial outgoing : State (ZMod p)) : ClosedVerifier (ZMod p) where
  name := "ordinary-observation"
  circuit := endpointCircuit initial outgoing
  assumptions := by intros; trivial
  lookups := by simp only [endpointCircuit, endpointMain, circuit_norm]
  public_interactions := by
    intro interaction member env
    simp only [endpointCircuit, endpointMain, circuit_norm, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;>
      simp [circuit_norm, ChannelInteraction.toRaw, AbstractInteraction.Requirements,
        Channel.toRaw, stateChannel, Expression.eval]
  length_zero := rfl
  constraints := by
    intros
    simp only [endpointCircuit, endpointMain, circuit_norm]
  interactions := by
    intro offset env channel
    exact (endpoint_values initial outgoing offset env channel).trans
      (endpoint_values initial outgoing 0 _ channel).symm

end SP1Clean.OrdinaryObservation
