import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.TypedState
import SP1Clean.Model.Semantics.Truth
import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.Model.Machine.Syscall
import Mathlib.Data.Set.Basic
import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Machine.Execution
import SP1Clean.Soundness.TypedSelectors

/-! # Typed Program fetches emitted by instruction rows

The Program bus is structural in the Clean circuit: instruction rows pull one decoded fetch and the
preprocessed Program table pushes matching rows.  This module keeps that exact typed interaction and
grounds it against the program named by the statement; no `LookupAccess` projection is introduced.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The Program message denoted by the chip-agnostic semantic row view. -/
def programMessageOfView (view : Trace.RowView (ZMod p)) : ProgramMsg (ZMod p) :=
  ⟨view.state.pc[0], view.state.pc[1], view.state.pc[2], view.opcode,
    view.adapter.op_a, view.adapter.op_b, view.adapter.op_c, view.adapter.op_a_0,
    view.adapter.imm_b, view.adapter.imm_c⟩

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
@[simp] theorem rowOfMsg_programMessageOfView (view : Trace.RowView (ZMod p)) :
    rowOfMsg (programMessageOfView view) = (programAccess view).toRow := rfl

/-- Exact Program emission for a typed circuit and its semantic row view.  There is one gated pull;
all committed-ROM meaning is established globally from the provider and channel balance. -/
def CircuitProgramEmissionShape {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ generation data physical,
    let component : Component (ZMod p) := { circuit := circuit, Assumptions := (circuit).Assumptions, generation }
    let env := Environment.fromArray physical data
    let rowView := view (component.rowInput env) (component.rowOutput env)
    component.operations.ConstraintsHold env →
      component.operations.interactionValuesWith programChannel.toRaw env =
        [programChannel.pulledIfValue rowView.is_real (programMessageOfView rowView)]

/-- Descriptor-level Program contract consumed by the deterministic witness decoder.  The physical
row must satisfy its own circuit constraints because some chips derive the public active selector
from an internal one-hot gate before emitting the fetch. -/
def ProgramEmissionShape (chip : SupportedChip p) : Prop :=
  ∀ data physical,
    let row := chip.decodeRow data physical
    let env := Environment.fromArray physical data
    chip.table.operations.ConstraintsHold env →
      chip.table.operations.interactionValuesWith programChannel.toRaw env =
        [programChannel.pulledIfValue row.is_real (programMessageOfView row.view)]

/-! ## Reader-local fetch interfaces

The per-reader Program payloads (`rTypeProgramMessage`, `aluTypeProgramMessage`,
`aluTypeImmutableProgramMessage`, `iTypeProgramMessage`, `iTypeImmutableProgramMessage`,
`jTypeProgramMessage`) and their exact/compositional interaction lemmas
(`<reader>_programInteractions` / `<reader>_programInteractions_subcircuit`) live next to each
reader's `circuit` in `Native/Readers/*.lean`, still inside this `SP1Clean.Soundness` namespace.
The channel-generic subcircuit helper is
`InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact`
(`Model/InteractionRecovery.lean`). -/

/-! ## Compositional interaction projection

Large chips should not have to normalize their entire monadic circuit merely to identify one bus
interaction.  `circuitInteractionsWith` projects a circuit onto one raw channel and the lemmas below
reduce that projection one bind or primitive at a time.  Arithmetic gadgets therefore remain opaque;
only their declared channel interfaces matter. -/

noncomputable def circuitInteractionsWith {F α} [FiniteField F]
    (channel : RawChannel F) (circuit : Circuit F α) (offset : ℕ) :
    List (AbstractInteraction F) :=
  circuit.operations offset |>.interactionsWith channel

theorem circuitInteractionsWith_bind {F α β} [FiniteField F]
    (channel : RawChannel F) (left : Circuit F α) (right : α → Circuit F β) (offset : ℕ) :
    circuitInteractionsWith channel (left >>= right) offset =
      circuitInteractionsWith channel left offset ++
        circuitInteractionsWith channel (right (left.output offset))
          (offset + left.localLength offset) := by
  change Operations.interactionsWith channel
      ((left offset).2 ++ (right (left offset).1
        (offset + Operations.localLength (left offset).2)).2) = _
  rw [Operations.interactionsWith_append]
  rfl

theorem assertion_localLength {F Input} [FiniteField F] [ProvableType Input]
    (circuit : FormalAssertion F Input) (input : Var Input F) (offset : ℕ) :
    (assertion circuit input).localLength offset = circuit.localLength input := by
  simp only [circuit_norm]

theorem generalAssertion_localLength {F Input Output} [FiniteField F]
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    (subcircuitWithAssertion circuit input).localLength offset = circuit.localLength input := by
  simp only [circuit_norm]

theorem circuitInteractionsWith_assertion_eq_nil {F Input} [FiniteField F]
    [ProvableType Input] (channel : RawChannel F) (circuit : FormalAssertion F Input)
    (input : Var Input F) (offset : ℕ)
    (hg : channel ∉ circuit.channelsWithGuarantees)
    (hr : channel ∉ circuit.channelsWithRequirements) :
    circuitInteractionsWith channel (assertion circuit input) offset = [] := by
  simpa only [circuitInteractionsWith, assertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      circuit channel input ([] : Operations F) hg hr)

theorem circuitInteractionsWith_generalAssertion_eq_nil {F Input Output} [FiniteField F]
    [ProvableType Input] [ProvableType Output]
    (channel : RawChannel F) (circuit : GeneralFormalCircuit F Input Output)
    (input : Var Input F) (offset : ℕ)
    (hg : channel ∉ circuit.channelsWithGuarantees)
    (hr : channel ∉ circuit.channelsWithRequirements) :
    circuitInteractionsWith channel (subcircuitWithAssertion circuit input) offset = [] := by
  simpa only [circuitInteractionsWith, subcircuitWithAssertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil
      circuit channel input ([] : Operations F) hg hr)

theorem circuitInteractionsWith_rTypeReader
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ) :
    circuitInteractionsWith programChannel.toRaw
        (subcircuitWithAssertion Readers.RTypeReader.circuit input) offset =
      [(programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw] := by
  simpa only [circuitInteractionsWith, subcircuitWithAssertion, Circuit.operations,
    Operations.interactionsWith_nil] using
    (rTypeReader_programInteractions_subcircuit input offset ([] : Operations (ZMod p)))

theorem circuitInteractionsWith_pure {F α} [FiniteField F]
    (channel : RawChannel F) (value : α) (offset : ℕ) :
    circuitInteractionsWith channel (pure value) offset = [] := by
  rfl

/-- Small syntactic interface identifying the circuit's unique Program pull and its semantic row
projection.  Concrete chip proofs normalize only abstract operations; evaluation is handled once by
`circuitProgramEmissionShape_of_contract`. -/
def CircuitProgramInteractionContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (gate : Var Input (ZMod p) → ℕ → Expression (ZMod p))
      (message : Var Input (ZMod p) → ℕ → ProgramMsg (Expression (ZMod p))),
    (∀ input offset,
      ((circuit.main input).operations offset).interactionsWith programChannel.toRaw =
        [(programChannel.pulledIf (gate input offset) (message input offset)).toRaw]) ∧
    (∀ env : Environment (ZMod p),
      ((circuit.instantiate.operations 0).ConstraintsHold env) →
        Eval.eval env (gate inputVar offset) =
          (view (Eval.eval env inputVar)
            (Eval.eval env (circuit.output inputVar offset))).is_real) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (message inputVar offset) =
      programMessageOfView (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset))))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluate a chip-local abstract Program contract into the exact typed physical-row emission. -/
theorem circuitProgramEmissionShape_of_contract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitProgramInteractionContract circuit view) :
    CircuitProgramEmissionShape circuit view := by
  obtain ⟨gate, message, interactions, gate_eval, message_eval⟩ := contract
  intro generation data physical
  dsimp only
  let component : Component (ZMod p) := { circuit := circuit, Assumptions := (circuit).Assumptions, generation }
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  intro constraints
  change component.operations.interactionValuesWith programChannel.toRaw env =
    [programChannel.pulledIfValue rowView.is_real (programMessageOfView rowView)]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((circuit.main inputVar).operations offset).interactionsWith programChannel.toRaw) = _
  rw [interactions inputVar offset]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf]
  rw [gate_eval env constraints, message_eval env]
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  rw [inputEq, outputEq]

/-- The small circuit-local interface identifying the chip's exposed Program pull with the semantic
row view — the Program sibling of `CircuitStateExposureContract` (`TypedState.lean`).  The single
membership fact rides the chip's public Clean `exposedChannels` interface, so per-chip proofs never
re-normalize the chip's subcircuit tree here; the gate evaluation may use the row's own constraints
because some chips derive the public active selector from internal one-hot flags. -/
def CircuitProgramExposureContract {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  ∃ (gate : Var Input (ZMod p) → ℕ → Expression (ZMod p))
      (message : Var Input (ZMod p) → ℕ → ProgramMsg (Expression (ZMod p))),
    (∀ input offset,
      ⟨programChannel.toRaw,
        [programChannel.pulledIf (gate input offset) (message input offset)].map
          ChannelInteraction.toRaw⟩ ∈ circuit.exposedChannels input offset) ∧
    (∀ env : Environment (ZMod p),
      ((circuit.instantiate.operations 0).ConstraintsHold env) →
        Eval.eval env (gate inputVar offset) =
          (view (Eval.eval env inputVar)
            (Eval.eval env (circuit.output inputVar offset))).is_real) ∧
    (∀ env : Environment (ZMod p), Eval.eval env (message inputVar offset) =
      programMessageOfView (view (Eval.eval env inputVar)
        (Eval.eval env (circuit.output inputVar offset))))

omit [Fact (2 ^ 24 < p)] in
/-- Reduce a chip's Program-emission contract to its public Clean exposed-channel interface and two
evaluation facts, mirroring `circuitStateEmissionShape_of_exposure`.  Callers never unfold the
chip's subcircuit tree, and the theorem still talks about the exact
`Operations.interactionValuesWith` list evaluated by Clean. -/
theorem circuitProgramEmissionShape_of_exposure {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p))
    (contract : CircuitProgramExposureContract circuit view) :
    CircuitProgramEmissionShape circuit view := by
  obtain ⟨gate, message, exposure, gate_eval, message_eval⟩ := contract
  intro generation data physical
  dsimp only
  let component : Component (ZMod p) := { circuit := circuit, Assumptions := (circuit).Assumptions, generation }
  let env := Environment.fromArray physical data
  let inputVar : Var Input (ZMod p) := varFromOffset Input 0
  let offset := size Input
  let rowView := view (component.rowInput env) (component.rowOutput env)
  intro constraints
  change component.operations.interactionValuesWith programChannel.toRaw env =
    [programChannel.pulledIfValue rowView.is_real (programMessageOfView rowView)]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval env)
      (((circuit.main inputVar).operations offset).interactionsWith programChannel.toRaw) = _
  rw [circuit.interactionsWith_eq_of_mem_exposedChannels inputVar offset _
    (exposure inputVar offset)]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf]
  rw [gate_eval env constraints, message_eval env]
  have inputEq : Eval.eval env inputVar = component.rowInput env :=
    eval_varFromOffset_valueFromOffset Input 0 env
  have outputEq : Eval.eval env (circuit.output inputVar offset) = component.rowOutput env := by
    simp only [component, Component.rowOutput, circuit_norm]
    rfl
  rw [inputEq, outputEq]

/-- Transport a circuit-local Program theorem to its retained supported-chip descriptor without
normalizing the dependent descriptor. -/
theorem programEmissionShape_of_circuit (kind : ChipKind p)
    (circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols)
    (generation : @WitnessGeneration.Generation (ZMod p) inferInstance kind.Inputs kind.provableInputs)
    (spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
      kind.provableInputs kind.provableCols circuit = kind.chipSpec)
    (id : InstructionChipId)
    (shape : @CircuitProgramEmissionShape p _ kind.Inputs kind.Cols kind.provableInputs
      kind.provableCols circuit kind.view) :
    ProgramEmissionShape ⟨id, kind, circuit, generation, spec_eq⟩ := by
  exact shape generation

/-- Lift a descriptor's Program contract to the typed interaction decoder. -/
theorem DecodedInstructionRow.programInteractions_eq
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data))
    (contract : ProgramEmissionShape decoded.chip) :
    decoded.interactionsWith data programChannel =
      [TypedInteraction.pulledIfValue programChannel (decoded.toChipRow data).is_real
        (programMessageOfView (decoded.toChipRow data).view)] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [DecodedInstructionRow.interactionsWith_raw]
  simpa only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw,
    DecodedInstructionRow.environment, DecodedInstructionRow.toChipRow] using
    contract data decoded.physical constraints


/-- Registry boilerplate: reduce a chip's Program-emission goal to the three exposure-contract
field goals. -/
local macro "programExposureStart" : tactic =>
  `(tactic| (
    apply circuitProgramEmissionShape_of_exposure
    unfold CircuitProgramExposureContract
    dsimp only))

/-- The shared closing normalization for chips whose Program exposure, gate, and fetch payload all
follow the plain reader template. -/
local macro "programExposureTail " circuit:term ", " rowView:term ", "
    adapterView:term : tactic =>
  `(tactic| (
    · intro input offset
      simp [$circuit:term, expose]
    · intro env
      simp [$circuit:term, $rowView:term, circuit_norm]
    · intro env
      simp [$circuit:term, $rowView:term, $adapterView:term,
        programMessageOfView, circuit_norm]))


theorem AddChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddChip.circuit (p := p)) AddChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 0,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  programExposureTail AddChip.circuit, AddChip.rowView, Circuits.Types.RTypeReader.toAdapterView

theorem AddiChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddiChip.circuit (p := p)) AddiChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 1,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  programExposureTail AddiChip.circuit, AddiChip.rowView, Circuits.Types.ITypeReader.toAdapterView

theorem AddwChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AddwChip.circuit (p := p)) AddwChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 19,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  programExposureTail AddwChip.circuit, AddwChip.rowView, Circuits.Types.ALUTypeReader.toAdapterView

theorem SubChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (SubChip.circuit (p := p)) SubChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 2,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  programExposureTail SubChip.circuit, SubChip.rowView, Circuits.Types.RTypeReader.toAdapterView

theorem SubwChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (SubwChip.circuit (p := p)) SubwChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 20,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  programExposureTail SubwChip.circuit, SubwChip.rowView, Circuits.Types.RTypeReader.toAdapterView

theorem BitwiseChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (BitwiseChip.circuit (p := p)) BitwiseChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], BitwiseChip.exposedOpcode input,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [BitwiseChip.circuit, BitwiseChip.exposedProgramInteractions, expose]
  · intro env
    simp [BitwiseChip.circuit, BitwiseChip.rowView, circuit_norm]
  · intro env
    simp [BitwiseChip.circuit, BitwiseChip.rowView, BitwiseChip.exposedOpcode,
      Circuits.Types.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem LtChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LtChip.circuit (p := p)) LtChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], LtChip.exposedOpcode input,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LtChip.circuit, LtChip.exposedProgramInteractions, expose]
  · intro env
    simp [LtChip.circuit, LtChip.rowView, circuit_norm]
  · intro env
    simp [LtChip.circuit, LtChip.rowView, LtChip.exposedOpcode,
      Circuits.Types.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem LoadDoubleChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadDoubleChip.circuit (p := p))
      LoadDoubleChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 35,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LoadDoubleChip.circuit, expose]
  · intro env
    simp [LoadDoubleChip.rowView, circuit_norm]
  · intro env
    simp [LoadDoubleChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem LoadByteChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadByteChip.circuit (p := p))
      LoadByteChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_lb + input.is_lbu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lb * 29 + input.is_lbu * 32, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LoadByteChip.circuit, expose]
  · intro env
    simp [LoadByteChip.rowView, LoadByteChip.isReal, circuit_norm]
  · intro env
    simp [LoadByteChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem LoadHalfChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadHalfChip.circuit (p := p))
      LoadHalfChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_lh + input.is_lhu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lh * 30 + input.is_lhu * 33, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LoadHalfChip.circuit, expose]
  · intro env
    simp [LoadHalfChip.rowView, LoadHalfChip.isReal, circuit_norm]
  · intro env
    simp [LoadHalfChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem LoadWordChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadWordChip.circuit (p := p))
      LoadWordChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_lw + input.is_lwu, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_lw * 31 + input.is_lwu * 34, input.adapter.op_a,
      #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LoadWordChip.circuit, expose]
  · intro env
    simp [LoadWordChip.rowView, LoadWordChip.isReal, circuit_norm]
  · intro env
    simp [LoadWordChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem LoadX0Chip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (LoadX0Chip.circuit (p := p))
      LoadX0Chip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
      input.is_lw + input.is_lwu + input.is_ld,
    fun input _ =>
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
        29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu +
          31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld,
        input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
        input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [LoadX0Chip.circuit, expose]
  · intro env
    simp [LoadX0Chip.rowView, LoadX0Chip.isReal, circuit_norm]
  · intro env
    simp [LoadX0Chip.rowView, LoadX0Chip.opcodeVal,
      Circuits.Types.ITypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem StoreByteChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreByteChip.circuit (p := p))
      StoreByteChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 36,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [StoreByteChip.circuit, expose]
  · intro env
    simp [StoreByteChip.rowView, circuit_norm]
  · intro env
    simp [StoreByteChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem StoreHalfChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreHalfChip.circuit (p := p))
      StoreHalfChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 37,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [StoreHalfChip.circuit, expose]
  · intro env
    simp [StoreHalfChip.rowView, circuit_norm]
  · intro env
    simp [StoreHalfChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem StoreWordChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreWordChip.circuit (p := p))
      StoreWordChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 38,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [StoreWordChip.circuit, expose]
  · intro env
    simp [StoreWordChip.rowView, circuit_norm]
  · intro env
    simp [StoreWordChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem StoreDoubleChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (StoreDoubleChip.circuit (p := p))
      StoreDoubleChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 39,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [StoreDoubleChip.circuit, expose]
  · intro env
    simp [StoreDoubleChip.rowView, circuit_norm]
  · intro env
    simp [StoreDoubleChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem AluX0Chip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (AluX0Chip.circuit (p := p))
      AluX0Chip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], input.opcode,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [AluX0Chip.circuit, AluX0Chip.exposedProgramInteractions, expose]
  · intro env
    simp [AluX0Chip.circuit, AluX0Chip.rowView, circuit_norm]
  · intro env
    simp [AluX0Chip.circuit, AluX0Chip.rowView,
      Circuits.Types.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem UTypeChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (UTypeChip.circuit (p := p)) UTypeChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      input.is_auipc * 48 + (1 - input.is_auipc) * 49,
      input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
      input.adapter.op_a_0, 1, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [UTypeChip.circuit, UTypeChip.exposedProgramInteractions, expose]
  · intro env
    simp [UTypeChip.circuit, UTypeChip.rowView, circuit_norm]
  · intro env
    simp [UTypeChip.circuit, UTypeChip.rowView, Circuits.Types.JTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem JalChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (JalChip.circuit (p := p)) JalChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 46,
      input.adapter.op_a, input.adapter.op_b_imm, input.adapter.op_c_imm,
      input.adapter.op_a_0, 1, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [JalChip.circuit, JalChip.exposedProgramInteractions, expose]
  · intro env
    simp [JalChip.circuit, JalChip.rowView, circuit_norm]
  · intro env
    simp [JalChip.circuit, JalChip.rowView, Circuits.Types.JTypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem JalrChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (JalrChip.circuit (p := p)) JalrChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 47,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [JalrChip.circuit, JalrChip.exposedProgramInteractions, expose]
  · intro env
    simp [JalrChip.circuit, JalrChip.rowView, circuit_norm]
  · intro env
    simp [JalrChip.circuit, JalrChip.rowView, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem BranchChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (BranchChip.circuit (p := p)) BranchChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], BranchChip.exposedOpcode input,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
      input.adapter.op_a_0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [BranchChip.circuit, BranchChip.stateExposure, Readers.CPUState.exposedState, expose]
  · intro env
    simp [BranchChip.circuit, BranchChip.rowView, circuit_norm]
  · intro env
    simp [BranchChip.circuit, BranchChip.rowView, BranchChip.branchOpcode,
      BranchChip.exposedOpcode, Circuits.Types.ITypeReader.toAdapterView,
      programMessageOfView, circuit_norm]

theorem ShiftLeftChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (ShiftLeftChip.circuit (p := p))
      ShiftLeftChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => ShiftLeftChip.exposedGate input,
    fun input _ =>
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
        ShiftLeftChip.exposedOpcode input,
        input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
        input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [ShiftLeftChip.circuit, ShiftLeftChip.stateExposure, Readers.CPUState.exposedState,
      expose]
  · intro env _
    simp [ShiftLeftChip.circuit, ShiftLeftChip.rowView, ShiftLeftChip.exposedGate,
      circuit_norm]
  · intro env
    simp [ShiftLeftChip.circuit, ShiftLeftChip.rowView, ShiftLeftChip.exposedOpcode,
      Circuits.Types.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem ShiftRightChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (ShiftRightChip.circuit (p := p))
      ShiftRightChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      ShiftRightChip.exposedOpcode input,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
      input.adapter.op_a_0, 0, input.adapter.imm_c⟩, ?_, ?_, ?_⟩
  · intro input offset
    simp [ShiftRightChip.circuit, ShiftRightChip.stateExposure,
      Readers.CPUState.exposedState, ShiftRightChip.exposedProgramInteractions, expose]
  · intro env _
    simp [ShiftRightChip.circuit, ShiftRightChip.rowView, circuit_norm]
  · intro env
    simp [ShiftRightChip.circuit, ShiftRightChip.rowView, ShiftRightChip.exposedOpcode,
      Circuits.Types.ALUTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem MulChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (MulChip.circuit (p := p)) MulChip.rowView := by
  programExposureStart
  refine ⟨fun input _ => input.is_real, fun input _ =>
    ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
      MulChip.exposedOpcode input,
      input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
      #v[input.adapter.op_c, 0, 0, 0], input.adapter.op_a_0, 0, 0⟩,
    ?_, ?_, ?_⟩
  · intro input offset
    simp [MulChip.circuit, MulChip.exposedStateInteractions,
      MulChip.exposedMemoryInteractions, MulChip.exposedProgramInteractions,
      expose]
  · intro env _
    simp [MulChip.circuit, MulChip.rowView, circuit_norm]
  · intro env
    simp [MulChip.circuit, MulChip.rowView, MulChip.exposedOpcode,
      Circuits.Types.RTypeReader.toAdapterView, programMessageOfView, circuit_norm]

theorem DivRemChip.programEmissionShape :
    CircuitProgramEmissionShape (p := p) (DivRemChip.circuit (p := p))
      DivRemChip.rowView := by
  apply circuitProgramEmissionShape_of_contract
  unfold CircuitProgramInteractionContract
  dsimp only
  refine ⟨fun input _ => input.is_real, DivRemChip.exposedProgramMessage, ?_, ?_, ?_⟩
  · intro input offset
    exact DivRemChip.interactionsWith_program_eq input offset
  · intro env _
    -- Reduce the view's projections before anything touches the 210-cell output.
    simp only [DivRemChip.rowView]
    simp [circuit_norm]
  · intro env
    simp only [DivRemChip.rowView]
    simp [DivRemChip.circuit, DivRemChip.exposedProgramMessage, ↓ DivRemChip.output_eq_populatedRowAt,
      DivRemChip.populatedRowAt_isDiv_eq, DivRemChip.populatedRowAt_isDivu_eq,
      DivRemChip.populatedRowAt_isRem_eq, DivRemChip.populatedRowAt_isRemu_eq,
      DivRemChip.populatedRowAt_isDivw_eq, DivRemChip.populatedRowAt_isRemw_eq,
      DivRemChip.populatedRowAt_isDivuw_eq, DivRemChip.populatedRowAt_isRemuw_eq,
      DivRemContract.encodedOpcode,
      Circuits.Types.RTypeReader.toAdapterView, programMessageOfView, circuit_norm]
    simp only [DivRemChip.Columns.eval_state, DivRemChip.Columns.eval_adapter,
      DivRemChip.Columns.eval_is_div, DivRemChip.Columns.eval_is_divu,
      DivRemChip.Columns.eval_is_rem, DivRemChip.Columns.eval_is_remu,
      DivRemChip.Columns.eval_is_divw, DivRemChip.Columns.eval_is_remw,
      DivRemChip.Columns.eval_is_divuw, DivRemChip.Columns.eval_is_remuw,
      DivRemChip.populatedRowAt_state_eq, DivRemChip.populatedRowAt_adapter_eq,
      DivRemChip.populatedRowAt_isDiv_eq, DivRemChip.populatedRowAt_isDivu_eq,
      DivRemChip.populatedRowAt_isRem_eq, DivRemChip.populatedRowAt_isRemu_eq,
      DivRemChip.populatedRowAt_isDivw_eq, DivRemChip.populatedRowAt_isRemw_eq,
      DivRemChip.populatedRowAt_isDivuw_eq, DivRemChip.populatedRowAt_isRemuw_eq, circuit_norm]

/-! ## Supported-machine registry -/

/-- Install a descriptor's retained dependent instances and transport its concrete circuit theorem
to the uniform supported-chip contract. -/
local macro "programRegistryCase " kind:term ", " shape:term : tactic =>
  `(tactic| (
    let _inputs := ($kind:term).provableInputs
    let _cols := ($kind:term).provableCols
    apply programEmissionShape_of_circuit
    exact $shape:term))

/-- Every instruction chip in the stable registry emits exactly one constraint-aligned Program pull
whose payload is its semantic row view. -/
theorem supportedChip_programEmissionShape (chip : SupportedChip p)
    (chipMem : chip ∈ supportedChips (p := p)) : ProgramEmissionShape chip := by
  fin_cases chipMem
  · programRegistryCase (AddChip.kind (p := p)), (AddChip.programEmissionShape (p := p))
  · programRegistryCase (AddiChip.kind (p := p)), (AddiChip.programEmissionShape (p := p))
  · programRegistryCase (AddwChip.kind (p := p)), (AddwChip.programEmissionShape (p := p))
  · programRegistryCase (SubChip.kind (p := p)), (SubChip.programEmissionShape (p := p))
  · programRegistryCase (SubwChip.kind (p := p)), (SubwChip.programEmissionShape (p := p))
  · programRegistryCase (BitwiseChip.kind (p := p)),
      (BitwiseChip.programEmissionShape (p := p))
  · programRegistryCase (LtChip.kind (p := p)), (LtChip.programEmissionShape (p := p))
  · programRegistryCase (ShiftLeftChip.kind (p := p)),
      (ShiftLeftChip.programEmissionShape (p := p))
  · programRegistryCase (ShiftRightChip.kind (p := p)),
      (ShiftRightChip.programEmissionShape (p := p))
  · programRegistryCase (JalChip.kind (p := p)), (JalChip.programEmissionShape (p := p))
  · programRegistryCase (JalrChip.kind (p := p)), (JalrChip.programEmissionShape (p := p))
  · programRegistryCase (BranchChip.kind (p := p)), (BranchChip.programEmissionShape (p := p))
  · programRegistryCase (UTypeChip.kind (p := p)), (UTypeChip.programEmissionShape (p := p))
  · programRegistryCase (LoadByteChip.kind (p := p)),
      (LoadByteChip.programEmissionShape (p := p))
  · programRegistryCase (LoadHalfChip.kind (p := p)),
      (LoadHalfChip.programEmissionShape (p := p))
  · programRegistryCase (LoadWordChip.kind (p := p)),
      (LoadWordChip.programEmissionShape (p := p))
  · programRegistryCase (LoadDoubleChip.kind (p := p)),
      (LoadDoubleChip.programEmissionShape (p := p))
  · programRegistryCase (LoadX0Chip.kind (p := p)),
      (LoadX0Chip.programEmissionShape (p := p))
  · programRegistryCase (StoreByteChip.kind (p := p)),
      (StoreByteChip.programEmissionShape (p := p))
  · programRegistryCase (StoreHalfChip.kind (p := p)),
      (StoreHalfChip.programEmissionShape (p := p))
  · programRegistryCase (StoreWordChip.kind (p := p)),
      (StoreWordChip.programEmissionShape (p := p))
  · programRegistryCase (StoreDoubleChip.kind (p := p)),
      (StoreDoubleChip.programEmissionShape (p := p))
  · programRegistryCase (MulChip.kind (p := p)), (MulChip.programEmissionShape (p := p))
  · programRegistryCase (DivRemChip.kind (p := p)),
      (DivRemChip.programEmissionShape (p := p))
  · programRegistryCase (AluX0Chip.kind (p := p)),
      (AluX0Chip.programEmissionShape (p := p))

/-- Every row retained by the canonical decoder inherits the registered Program contract. -/
theorem DecodedInstructionRow.programEmissionShape_of_mem
    (decoded : DecodedInstructionRow p) (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    ProgramEmissionShape decoded.chip :=
  supportedChip_programEmissionShape decoded.chip
    (decodedInstructionRows_chip_mem tables decodedMem)

/-- A constrained canonical row exposes its actual Program interactions as the one semantic fetch. -/
theorem DecodedInstructionRow.programInteractions_eq_of_mem
    (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p)))
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables)
    (constraints : decoded.chip.table.operations.ConstraintsHold (decoded.environment data)) :
    decoded.interactionsWith data programChannel =
      [TypedInteraction.pulledIfValue programChannel (decoded.toChipRow data).is_real
        (programMessageOfView (decoded.toChipRow data).view)] :=
  decoded.programInteractions_eq data constraints
    (decoded.programEmissionShape_of_mem tables decodedMem)

/-! ## Ensemble-level Program grounding -/

/-- The public State-boundary verifier does not participate in the Program channel. -/
theorem witness_verifierProgramInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedInteractionValuesWith (sp1Ensemble (p := p)).verifierOperations programChannel
      witness.data.publicEnvironment = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedInteractionValuesWith_raw]
  simp only [sp1Ensemble, Ensemble.verifierOperations, sp1StateVerifierProgram,
    Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.ofInteractions_values]
  simp [Operations.interactionValuesWith, sp1StateVerifierMain, circuit_norm]

/-- The decoded instruction prefix's Program interactions are exactly one semantic gated pull per
physical row. -/
theorem decodedWitnessProgramInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables programChannel =
      (decodedInstructionRows (p := p) witness.tables).flatMap fun decoded =>
        [TypedInteraction.pulledIfValue programChannel
          (decoded.toChipRow witness.data).is_real
          (programMessageOfView (decoded.toChipRow witness.data).view)] := by
  unfold decodedWitnessInstructionInteractionsWith decodedInstructionInteractionsWith
  apply List.flatMap_congr
  intro decoded decodedMem
  exact decoded.programInteractions_eq_of_mem witness.data witness.tables decodedMem
    (decodedInstructionRow_constraints witness constraints decoded decodedMem)

/-- Every decoded Program interaction is a disabled row or an active pull. -/
theorem decodedWitnessProgramInteractions_pullShape
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ interaction ∈
        decodedWitnessInstructionInteractionsWith witness.data witness.tables programChannel,
      interaction.mult = 0 ∨ interaction.raw.Pull := by
  rw [decodedWitnessProgramInteractions_eq witness constraints]
  intro interaction interactionMem
  obtain ⟨decoded, decodedMem, interactionMem⟩ := List.mem_flatMap.mp interactionMem
  simp only [List.mem_singleton] at interactionMem
  subst interaction
  rcases witness_decodedInstructionRows_selectorBinary witness constraints decoded decodedMem with
    disabled | active
  · left
    rw [TypedInteraction.pulledIfValue_mult, disabled]
  · right
    exact ⟨rfl, active⟩

end SP1Clean.Soundness
