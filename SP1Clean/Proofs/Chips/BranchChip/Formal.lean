import SP1Clean.Native.Witgen.StateDemand
import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection
import SP1Clean.Proofs.Chips.BranchChip.Core

/-! # `SP1Clean.BranchChip` — circuit packaging and audited channel exposure

Perf: the former 2M/4M budgets on the two channel-law theorems were ~50–100× over; both floor
at ≤40000. -/

namespace SP1Clean.BranchChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem main_requirementsChannelsLawful
    (input_var : Var Inputs (ZMod p)) (i₀ : ℕ) :
    ((main input_var).operations i₀).RequirementsChannelsLawful
      (elaborated (p := p)).channelsWithGuarantees
      [(memoryChannel (p := p)).toRaw] := by
  have h_byte : (byteChannel (p := p)).toRaw ∈
      (elaborated (p := p)).channelsWithGuarantees := by
    simp only [circuit_norm]
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_witness,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_assert,
      Operations.subcircuitChannelsWithRequirements_interact,
      Operations.subcircuitChannelsWithRequirements_nil,
      GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
      FormalAssertion.toSubcircuit_channelsWithRequirements,
      Readers.CPUState.channelsWithRequirements_eq, LtOperationSigned.circuit,
      Readers.ITypeReaderImmutable.circuit, Gadgets.Equality.channelsWithRequirements_eq,
      List.nil_append, List.append_nil]
    simp only [List.subset_def, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro channel h_channel
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def, witnessVectorIR, witnessField, Witnessable.witness, witnessIR, subcircuitWithAssertion, assertion, assertZero,
      Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength] at h_channel
    simp only [Operations.shallowChannels_append, Operations.shallowChannels_witness,
      Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
      Operations.shallowChannels_interact, Operations.shallowChannels_nil,
      List.nil_append] at h_channel
    simp only [ChannelInteraction.toRaw_channel, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false, or_self] at h_channel
    subst channel
    exact Or.inl h_byte
  · intro env h_constraints
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def, witnessVectorIR, witnessField, Witnessable.witness, witnessIR, subcircuitWithAssertion, assertion, assertZero,
      Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength] at h_constraints
    simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, true_and, and_true, eval_sub, Expression.eval] at h_constraints
    have h_bool : Expression.eval env input_var.is_real = 0 ∨
        Expression.eval env input_var.is_real = 1 :=
      bool_of_mul_pred h_constraints.1
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro interaction h_interaction
    simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def, witnessVectorIR, witnessField, Witnessable.witness, witnessIR, subcircuitWithAssertion, assertion, assertZero,
      Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength] at h_interaction
    simp only [Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
      Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
      Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
      List.nil_append] at h_interaction
    simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl | rfl <;>
      right <;>
      exact h_bool

/-- The Program-fetch opcode selected by the six input discriminants. -/
def exposedOpcode (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.isBeq * 40 + input.isBne * 41 + input.isBlt * 42 +
    input.isBge * 43 + input.isBltu * 44 + input.isBgeu * 45

/-- Branch's exact Memory-channel list, descended from `ITypeReaderImmutable`. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (_offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
        input.adapter.op_a_memory.access_timestamp.prev_low,
        input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
        input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
        input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
        input.adapter.op_b_memory.access_timestamp.prev_low,
        input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
        input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
        input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ]

omit [Fact (2 ^ 17 < p)] in
theorem opAPull_mem_exposedMemoryInteractions
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
        input.adapter.op_a_memory.access_timestamp.prev_low,
        input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
theorem opBPull_mem_exposedMemoryInteractions
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
        input.adapter.op_b_memory.access_timestamp.prev_low,
        input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- State, Memory, and Program interactions exposed by the exact Branch row.
`next_pc` occupies local cells `offset + 11 .. offset + 13`. -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state,
      #v[var ⟨offset + 11⟩, var ⟨offset + 12⟩, var ⟨offset + 13⟩],
      8, input.is_real⟩ ++
  expose memoryChannel (exposedMemoryInteractions input offset) ++
  expose programChannel
    [ programChannel.pulledIf input.is_real
        ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
          exposedOpcode input, input.adapter.op_a,
          #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
          input.adapter.op_a_0, 0, 1⟩ ]

private theorem main_exposedChannelsLawful
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful
      (stateExposure input offset) := by
  unfold Operations.ExposedChannelsLawful
  intro exposed exposedMem
  simp only [stateExposure, Readers.CPUState.exposedState, expose,
    List.mem_append, List.mem_singleton] at exposedMem
  rcases exposedMem with (rfl | rfl) | rfl
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      Readers.CPUState.interactionsWith_state_subcircuit,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil, LtOperationSigned.circuit,
      LtOperationSigned.channelsWithGuarantees_eq, Readers.ITypeReaderImmutable.circuit,
      Readers.ITypeReaderImmutable.channelsWithGuarantees_eq,
      FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
      Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
      Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
      Operations.interactionsWith_assert, Operations.interactionsWith_interact,
      Operations.interactionsWith_nil, List.nil_append]
    simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
      Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_stateChannel_false, ite_false, List.append_nil]
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_witness,
      Soundness.iTypeReaderImmutable_memoryInteractions_subcircuit,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil, LtOperationSigned.circuit,
      LtOperationSigned.channelsWithGuarantees_eq, Readers.CPUState.circuit,
      Readers.CPUState.channelsWithGuarantees_eq, Gadgets.Equality.channelsWithGuarantees_eq,
      Gadgets.Equality.channelsWithRequirements_eq, FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false, Channels.memoryChannel_eq_byteChannel_false,
      Channels.memoryChannel_eq_stateChannel_false, not_false_eq_true,
      Operations.interactionsWith_assert, Operations.interactionsWith_interact,
      Operations.interactionsWith_nil, Soundness.iTypeImmutableMemoryInteractions,
      List.cons_append, List.nil_append]
    simp only [circuit_norm]
    simp only [Channels.byteChannel_eq_memoryChannel_false, ite_false,
      exposedMemoryInteractions, List.map_cons, List.map_nil]
    rfl
  · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
      witnessVectorIR, witnessField, Witnessable.witness, witnessIR,
      subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
      InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
      InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
      Soundness.iTypeReaderImmutable_programInteractions_subcircuit, LtOperationSigned.circuit,
      LtOperationSigned.channelsWithGuarantees_eq, Readers.CPUState.circuit,
      Readers.CPUState.channelsWithGuarantees_eq, FormalCircuitBase.channelsWithGuarantees_def,
      List.mem_cons, List.not_mem_nil, or_false, Channels.programChannel_eq_byteChannel_false,
      Channels.programChannel_eq_stateChannel_false, not_false_eq_true,
      Operations.interactionsWith_assert, Operations.interactionsWith_interact,
      Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
      Soundness.iTypeImmutableProgramMessage, exposedOpcode]
    simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
      Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
    simp only [Channels.byteChannel_eq_programChannel_false, ite_false, List.nil_append]

omit [Fact (2 ^ 17 < p)] in
private theorem comparison_congr (input : Var Inputs (ZMod p))
    (env env' : ProverEnvironment (ZMod p))
    (h_input : ProvableStruct.eval env.toEnvironment input =
      ProvableStruct.eval env'.toEnvironment input) :
    (Witgen.WitgenIR.ofCompositeFExpr (LtOperationSigned.populateFE #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
        input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]
      #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
      (input.isBlt + input.isBge) input.is_real)).eval env =
      (Witgen.WitgenIR.ofCompositeFExpr (LtOperationSigned.populateFE #v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
        input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]]
      #v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]]
      (input.isBlt + input.isBge) input.is_real)).eval env' := by
  refine LtOperationSigned.populateIR_congr env env' _ _ _ _
    (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_a_memory.prev_value) h_input
    rw [eval_rs1In, eval_rs1In] at hv
    have hi' := congrArg (fun v : Word (ZMod p) => v[i]) hv
    interval_cases i <;> simpa only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ProvableType.getElem_eval_fields] using hi'
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
    rw [eval_rs2In, eval_rs2In] at hv
    have hi' := congrArg (fun v : Word (ZMod p) => v[i]) hv
    interval_cases i <;> simpa only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ProvableType.getElem_eval_fields] using hi'
  · simp only [circuit_norm, h_input]
  · simpa only [eval_isReal] using congrArg Inputs.is_real h_input

/-- The exact pinned-SP1 Branch `GeneralFormalCircuit`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { name := "sp1.native.branch", main, elaborated,
    computableWitnesses := by
      preserve_tactic_target
      intro n input env env'
      constructor
      · simp only [main, circuit_norm, Nat.add_zero,
          Gadgets.Equality.toSubcircuit_computableWitnesses]
        repeat' apply And.intro
        all_goals intro h_input
        all_goals first
          | exact Subcircuit.computableWitnesses_of_localLength_zero _ _ _ _ rfl
          | intro h_agree
            first
              | exact comparison_congr input env env' h_input
              | -- Decision from selectors and the comparison cells already written.
                simp (disch := omega) only [branchDecision, circuit_norm,
                  Inputs.eval_congr_isBeq h_input, Inputs.eval_congr_isBne h_input,
                  Inputs.eval_congr_isBlt h_input, Inputs.eval_congr_isBge h_input,
                  Inputs.eval_congr_isBltu h_input, Inputs.eval_congr_isBgeu h_input,
                  h_agree.get_eq]
              | -- The three `next_pc` cells: pc/imm inputs, the `is_branching` cell below, `is_real`.
                refine nextPcIR_congr env env' _ _ _ _ (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
                · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_state h_input]
                · interval_cases i <;> simp only [circuit_norm, Inputs.eval_congr_adapter h_input]
                · simp only [circuit_norm]
                  exact h_agree.get_eq (by omega)
                · simpa only [eval_isReal] using congrArg Inputs.is_real h_input
      · intro h h_agrees
        simp only [CircuitType.eval_var_prover_to_verifier, ProvableStruct.eval_eq_eval] at h
        have length_eq : (main input).localLength n = 14 :=
          (elaborated.localLength_eq input n).trans (by rfl)
        rw [length_eq] at h_agrees
        rw [elaborated.output_eq]
        simp (disch := omega) only [circuit_norm, h, h_agrees.get_eq]
        repeat' apply And.intro
        all_goals
          apply Vector.ext
          intro i hi
          simp (disch := omega) only [circuit_norm, h_agrees.get_eq],
    channelsWithRequirements := [memoryChannel.toRaw],
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    ProverSpec := fun _ _ _ => True,
    soundness := soundness,
    completeness := completeness,
    requirementsChannelsLawful := main_requirementsChannelsLawful,
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

@[circuit_norm] theorem circuit_main_eq :
    (circuit (p := p)).main = main := rfl

/-- The completed Branch circuit exposes exactly its immutable-reader Memory list. -/
theorem interactionsWith_memory_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map
        ChannelInteraction.toRaw := by
  exact main_exposedChannelsLawful input offset
    ⟨memoryChannel.toRaw,
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [stateExposure, Readers.CPUState.exposedState, expose])

/-- The row contains no Clean lookup operations; cross-table checks use channels. -/
theorem lookups_empty :
    ((circuit (p := p)).instantiate.operations 0).lookups = [] := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit,
    Operations.toNested_toFlat]
  simp [BranchChip.main, LtOperationSigned.circuit,
    LtOperationSigned.main, U16MSBOperation.circuit,
    U16MSBOperation.main, LtOperationUnsigned.circuit,
    LtOperationUnsigned.main, U16CompareOperation.circuit,
    U16CompareOperation.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.ITypeReaderImmutable.circuit,
    Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    Gadgets.Equality.main, circuit_norm]

/-- Upstream Clean creates one row per active State request using the shared hint layout. -/
def generation : Air.Flat.WitnessGeneration.Generation (ZMod p) Inputs :=
  Native.Witgen.stateDemand (circuit (p := p)).name (fun input : Inputs (Witgen.FExpr (ZMod p)) => input.state)
    (fun input => input.is_real)

end SP1Clean.BranchChip
