import SP1Clean.Native.Chips.HostHintLengthChip.Defs
import Clean.Utils.Tactics

/-! # Soundness and completeness of the current-head HINT_LEN handler

Local node guarantees supply representation bounds, while the explicit node binding in the
semantic bridge remains an assembly obligation. The complete handler contract supplies local
completeness; no prover-supplied zero selector or clock comparison is trusted.
-/

namespace SP1Clean.HostHintLengthChip

open Circuit HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def circuit (empty : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := if empty then "sp1.native.hint_len.empty" else "sp1.native.hint_len.nonempty"
  main := main empty
  elaborated := elaborated empty
  computableWitnesses := by
    cases empty <;> computable_witnesses [Inputs.clock]
  Spec input _ _ := Spec empty input
  ProverAssumptions input _ _ := Spec empty input
  channelsWithRequirements :=
    [HostCallChip.channel.toRaw, stateChannel.toRaw] ++ (if empty then [] else [nodeChannel.toRaw])
  soundness := by
    circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit,
      HostCallChip.channel, stateChannel, nodeChannel, Inputs.clock, Inputs.next]
    cases empty <;> simp only [Bool.false_eq_true, ↓reduceIte, Vector.map_id', circuit_norm,
      HeadSpec] at *
    all_goals simpa only [h_input] using h_holds
  completeness := by
    circuit_proof_start [Gadgets.Equality.circuit, ClockOrder.circuit,
      HostCallChip.channel, stateChannel, nodeChannel, Inputs.clock, Inputs.next]
    cases empty <;> simp only [Bool.false_eq_true, ↓reduceIte, Vector.map_id', circuit_norm,
      HeadSpec] at *
    all_goals simpa only [h_input] using h_assumptions
  requirementsChannelsLawful := by
    preserve_tactic_target
    cases empty
    all_goals
      intro input offset
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, circuit_norm, HostCallChip.channel, stateChannel, nodeChannel,
          ClockOrder.circuit, Gadgets.Equality.circuit]
      · simp only [main, circuit_norm, HostCallChip.channel, stateChannel, nodeChannel,
          ClockOrder.circuit, Gadgets.Equality.circuit]
        tauto
      · intro env _
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction member
        apply Or.inl
        have selected := List.mem_map_of_mem (f := fun item : AbstractInteraction (ZMod p) => item.channel) member
        rw [← Operations.shallowChannels_eq_interactions_map] at selected
        simpa only [main, circuit_norm, or_comm, or_left_comm] using selected

end SP1Clean.HostHintLengthChip
