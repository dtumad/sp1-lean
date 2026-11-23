import ToClean.Air.Authentication
import SP1Clean.Native.Operations.WriteProbeAccess
import SP1Clean.Soundness.ProtectedOrdinaryReceipt

/-! # WRITE predecessor sources from every protected ordinary instruction

Each instruction reuses its exact existing typed Memory exposure and its actual incoming CPU
state. Appending private receipts leaves all-original multiplicities and row widths intact.
-/

namespace SP1Clean.WriteProbe.OrdinarySources

open Circuit Air.Flat Soundness Channels AccessSupply

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Use the registered instruction input representation without unfolding its circuit. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs

/-- Use the registered column representation for the instruction output. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

/-- Exact symbolic exposures from the original twenty-five instruction circuits. -/
def layout : (id : InstructionChipId) → Layout p (supportedChipFor (p := p) id).kind.Inputs
  | .add => ⟨AddChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .addi => ⟨AddiChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .addw => ⟨AddwChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .sub => ⟨SubChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .subw => ⟨SubwChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .bitwise => ⟨BitwiseChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .lt => ⟨LtChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .shiftLeft => ⟨ShiftLeftChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .shiftRight => ⟨ShiftRightChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .jal => ⟨JalChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .jalr => ⟨JalrChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .branch => ⟨BranchChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .uType => ⟨UTypeChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .loadByte => ⟨LoadByteChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .loadHalf => ⟨LoadHalfChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .loadWord => ⟨LoadWordChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .loadDouble => ⟨LoadDoubleChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .loadX0 => ⟨LoadX0Chip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .storeByte => ⟨StoreByteChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .storeHalf => ⟨StoreHalfChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .storeWord => ⟨StoreWordChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .storeDouble => ⟨StoreDoubleChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .mul => ⟨MulChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .divRem => ⟨DivRemChip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩
  | .aluX0 => ⟨AluX0Chip.exposedMemoryInteractions, fun input => cpuStatePullMessage input.state⟩

/-- Exact number of private source occurrences on one physical ordinary row. -/
def accessCount (id : InstructionChipId) : ℕ := (layout (p := p) id).count

/-- Every padding or active ordinary row contributes between one and three private occurrences. -/
theorem accessCount_bounds (id : InstructionChipId) : 1 ≤ accessCount (p := p) id ∧ accessCount (p := p) id ≤ 3 := by
  cases id <;> first | exact (by decide : 1 ≤ 1 ∧ 1 ≤ 3) | exact (by decide : 1 ≤ 2 ∧ 2 ≤ 3) | exact (by decide : 1 ≤ 3 ∧ 3 ≤ 3)

/-- Instantiating at a different offset changes cells and expressions but preserves all pull positions. -/
theorem fixedShape (id : InstructionChipId) : (layout (p := p) id).FixedShape := by
  intro input offset
  cases id <;> rfl

/-- The source list is precisely the original installed Memory ledger before protection. -/
theorem original_memory (id : InstructionChipId) (input : Var (supportedChipFor (p := p) id).kind.Inputs (ZMod p))
    (offset : ℕ) : (((supportedChipFor id).circuit.main input).operations offset).interactionsWith memoryChannel.toRaw =
      ((layout id).memory input offset).map ChannelInteraction.toRaw := by
  cases id with
  | add => exact AddChip.interactionsWith_memory_eq input offset
  | addi => exact AddiChip.interactionsWith_memory_eq input offset
  | addw => exact AddwChip.interactionsWith_memory_eq input offset
  | sub => exact SubChip.interactionsWith_memory_eq input offset
  | subw => exact SubwChip.interactionsWith_memory_eq input offset
  | bitwise => exact BitwiseChip.interactionsWith_memory_eq input offset
  | lt => exact LtChip.interactionsWith_memory_eq input offset
  | shiftLeft => exact ShiftLeftChip.interactionsWith_memory_eq input offset
  | shiftRight => exact ShiftRightChip.interactionsWith_memory_eq input offset
  | jal => exact JalChip.interactionsWith_memory_eq input offset
  | jalr => exact JalrChip.interactionsWith_memory_eq input offset
  | branch => exact BranchChip.interactionsWith_memory_eq input offset
  | uType => exact UTypeChip.interactionsWith_memory_eq input offset
  | loadByte => exact LoadByteChip.interactionsWith_memory_eq input offset
  | loadHalf => exact LoadHalfChip.interactionsWith_memory_eq input offset
  | loadWord => exact LoadWordChip.interactionsWith_memory_eq input offset
  | loadDouble => exact LoadDoubleChip.interactionsWith_memory_eq input offset
  | loadX0 => exact LoadX0Chip.interactionsWith_memory_eq input offset
  | storeByte => exact StoreByteChip.interactionsWith_memory_eq input offset
  | storeHalf => exact StoreHalfChip.interactionsWith_memory_eq input offset
  | storeWord => exact StoreWordChip.interactionsWith_memory_eq input offset
  | storeDouble => exact StoreDoubleChip.interactionsWith_memory_eq input offset
  | mul => exact MulChip.interactionsWith_memory_eq input offset
  | divRem => exact DivRemChip.interactionsWith_memory_eq input offset
  | aluX0 => exact AluX0Chip.interactionsWith_memory_eq input offset

/-- The projected upper clock is the decoded row's incoming State, including control-flow rows. -/
def IncomingAgrees {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (provider : GeneralFormalCircuit (ZMod p) Input Output) (locations : Layout p Input)
    (view : Input (ZMod p) → Output (ZMod p) → Trace.RowView (ZMod p)) : Prop :=
  ∀ (input : Var Input (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)),
    eval env (locations.incoming input) = statePullOfView (view (eval env input)
      (eval env (provider.output input offset)))

local macro "incomingRow " circuit:term ", " view:term ", " source:term : tactic =>
  `(tactic| (
    change IncomingAgrees $circuit:term (layout $source:term) $view:term
    intro input offset env
    dsimp only [layout]
    first
    | solve | simp only [$view:term, statePullOfView, stateAccess, cpuStatePullMessage, circuit_norm]
    | simp only [$circuit:term, $view:term, statePullOfView, stateAccess, cpuStatePullMessage, circuit_norm]))

/-- Every projection uses the instruction's authentic incoming clock. -/
theorem incoming_agrees (id : InstructionChipId) :
    IncomingAgrees (supportedChipFor (p := p) id).circuit (layout id) (supportedChipFor id).kind.view := by
  cases id with
  | add => incomingRow AddChip.circuit, AddChip.rowView, .add
  | addi => incomingRow AddiChip.circuit, AddiChip.rowView, .addi
  | addw => incomingRow AddwChip.circuit, AddwChip.rowView, .addw
  | sub => incomingRow SubChip.circuit, SubChip.rowView, .sub
  | subw => incomingRow SubwChip.circuit, SubwChip.rowView, .subw
  | bitwise => incomingRow BitwiseChip.circuit, BitwiseChip.rowView, .bitwise
  | lt => incomingRow LtChip.circuit, LtChip.rowView, .lt
  | shiftLeft => incomingRow ShiftLeftChip.circuit, ShiftLeftChip.rowView, .shiftLeft
  | shiftRight => incomingRow ShiftRightChip.circuit, ShiftRightChip.rowView, .shiftRight
  | jal => incomingRow JalChip.circuit, JalChip.rowView, .jal
  | jalr => incomingRow JalrChip.circuit, JalrChip.rowView, .jalr
  | branch => incomingRow BranchChip.circuit, BranchChip.rowView, .branch
  | uType => incomingRow UTypeChip.circuit, UTypeChip.rowView, .uType
  | loadByte => incomingRow LoadByteChip.circuit, LoadByteChip.rowView, .loadByte
  | loadHalf => incomingRow LoadHalfChip.circuit, LoadHalfChip.rowView, .loadHalf
  | loadWord => incomingRow LoadWordChip.circuit, LoadWordChip.rowView, .loadWord
  | loadDouble => incomingRow LoadDoubleChip.circuit, LoadDoubleChip.rowView, .loadDouble
  | loadX0 => incomingRow LoadX0Chip.circuit, LoadX0Chip.rowView, .loadX0
  | storeByte => incomingRow StoreByteChip.circuit, StoreByteChip.rowView, .storeByte
  | storeHalf => incomingRow StoreHalfChip.circuit, StoreHalfChip.rowView, .storeHalf
  | storeWord => incomingRow StoreWordChip.circuit, StoreWordChip.rowView, .storeWord
  | storeDouble => incomingRow StoreDoubleChip.circuit, StoreDoubleChip.rowView, .storeDouble
  | mul => incomingRow MulChip.circuit, MulChip.rowView, .mul
  | divRem =>
    incomingRow DivRemChip.circuit, DivRemChip.rowView, .divRem
    simp only [DivRemChip.Columns.eval_state, circuit_norm]
  | aluX0 => incomingRow AluX0Chip.circuit, AluX0Chip.rowView, .aluX0

/-- Attach one gated publication per actual physical pull to the permission- and State-protected circuit. -/
def component (id : InstructionChipId) : Component (ZMod p) where
  circuit := (layout id).circuit (fixedShape id) (ProtectedOrdinaryReceipt.component id).circuit
  generation := (supportedChipFor id).generation
  Assumptions := (ProtectedOrdinaryReceipt.component id).Assumptions
  circuit_assumptions_of_assumptions := by
    intro i input data fixed declared holds
    have preserved := Receipt.many_assumptions (ProtectedOrdinaryReceipt.component (p := p) id).circuit
      readbackChannel (fun _ _ => trivial) ((layout id).projections (fixedShape id))
    exact (congrFun (congrFun preserved input) data).mpr holds

/-- All original channel occurrences, including original Memory and permission checks, survive. -/
theorem interactions (id : InstructionChipId) (channel : RawChannel (ZMod p))
    (different : channel ≠ readbackChannel.toRaw) :
    (component id).operations.interactionsWith channel =
      (ProtectedOrdinaryReceipt.component id).operations.interactionsWith channel :=
  Receipt.many_interactions _ _ (fun _ _ => trivial) _ channel different

theorem width (id : InstructionChipId) : (component (p := p) id).width = (ProtectedOrdinaryReceipt.component (p := p) id).width :=
  Receipt.many_width _ _ (fun _ _ => trivial) _

theorem constraints (id : InstructionChipId) : (component (p := p) id).operations.constraints =
    (ProtectedOrdinaryReceipt.component id).operations.constraints := Receipt.many_constraints _ _ (fun _ _ => trivial) _

theorem lookups (id : InstructionChipId) : (component (p := p) id).operations.lookups =
    (ProtectedOrdinaryReceipt.component id).operations.lookups := Receipt.many_lookups _ _ (fun _ _ => trivial) _

private theorem missing (id : InstructionChipId) :
    readbackChannel.toRaw ∉ (supportedChipFor (p := p) id).circuit.channels := by
  have member : (supportedChipFor (p := p) id).table ∈ sp1Tables :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨id, InstructionChipId.mem_all id, rfl⟩, rfl⟩
  intro present
  have used := sp1Tables_channels_subset _ member present
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false] at used
  rcases used with used | used | used | used | used <;>
    exact Bool.noConfusion (congrArg (fun channel => channel.name == "sp1.native.write_readback") used)

private theorem protected_silent (id : InstructionChipId) :
    (ProtectedOrdinaryReceipt.component (p := p) id).operations.interactionsWith readbackChannel.toRaw = [] := by
  rw [ProtectedOrdinaryReceipt.interactions id _ (by
        intro same
        exact Bool.noConfusion (congrArg (fun channel => channel.name == "sp1.native.write_readback") same)),
      ProtectedOrdinaryReceipt.provider_interactions id _ (by
        intro same
        exact Bool.noConfusion (congrArg (fun channel => channel.name == "sp1.native.write_readback") same))]
  simp only [Component.interactionsWith_eq, Component.rowOperations]
  exact InteractionRecovery.interactionsWith_main_eq_nil (supportedChipFor (p := p) id).circuit.base _
    (varFromOffset (supportedChipFor (p := p) id).kind.Inputs 0) (size (supportedChipFor (p := p) id).kind.Inputs)
    (missing id)

/-- Exactly one physically counted publication for each pull. There is no additional private source
on the protected ordinary row. The original multiplicity is preserved, even when it is zero. -/
theorem row_receipts (id : InstructionChipId) (env : Environment (ZMod p)) :
    let input := varFromOffset (F := ZMod p) (supportedChipFor (p := p) id).kind.Inputs 0
    let offset := size (supportedChipFor (p := p) id).kind.Inputs
    (component id).operations.interactionValuesWith readbackChannel.toRaw env =
      ((layout id).pulls input offset).map (fun i => readbackChannel.pushedIfValue (env i.mult)
        (readback (eval env ((layout id).incoming input)) (eval env i.msg))) := by
  let input := varFromOffset (F := ZMod p) (supportedChipFor (p := p) id).kind.Inputs 0
  let offset := size (supportedChipFor (p := p) id).kind.Inputs
  have added := (layout id).added (fixedShape id) (ProtectedOrdinaryReceipt.component (p := p) id).circuit input offset
  have original := protected_silent (p := p) id
  simp only [Component.interactionsWith_eq, Component.rowOperations] at original
  change (((ProtectedOrdinaryReceipt.component id).circuit.main input).operations offset).interactionsWith readbackChannel.toRaw = [] at original
  rw [original, List.nil_append] at added
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
  change ((((component id).circuit.main input).operations offset).interactionsWith readbackChannel.toRaw).map (AbstractInteraction.eval env) = _
  rw [show (((component id).circuit.main input).operations offset).interactionsWith readbackChannel.toRaw = _ from added]
  simp only [List.map_map, Function.comp_def, Channel.eval_pushedIf, ProvableType.eval_field, eval_readback, input, offset]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation of a typed Memory pull preserves its original gate and complete message. -/
theorem evaluated_pull (env : Environment (ZMod p)) (i : ChannelInteraction (memoryChannel (p := p)))
    (direction : i.direction = .pull) :
    i.toRaw.eval env = memoryChannel.pulledIfValue (env i.mult) (eval env i.msg) := by
  obtain ⟨direction', mult, msg⟩ := i
  change direction' = .pull at direction
  subst direction'
  exact (Channel.eval_pulledIf (channel := memoryChannel) (enabled := mult) (msg := msg) (env := env)).trans
    (congrArg (fun gate => memoryChannel.pulledIfValue gate (eval env msg)) (ProvableType.eval_field env mult))

/-- The private publication site is a genuine pull on the original protected Memory ledger. -/
theorem protected_pull (id : InstructionChipId) (env : Environment (ZMod p))
    (i : ChannelInteraction (memoryChannel (p := p)))
    (occurs : i ∈ (layout id).pulls (varFromOffset _ 0) (size (supportedChipFor (p := p) id).kind.Inputs)) :
    memoryChannel.pulledIfValue (env i.mult) (eval env i.msg) ∈
      (ProtectedOrdinaryReceipt.component id).operations.interactionValuesWith memoryChannel.toRaw env := by
  obtain ⟨member, direction⟩ := List.mem_filter.mp occurs
  have pulled := evaluated_pull env i (beq_iff_eq.mp direction)
  simp only [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions id (memoryChannel (p := p)).toRaw (by
      intro same
      exact Bool.noConfusion (congrArg (fun channel => channel.name == "SP1Memory") same)),
    ProtectedOrdinaryReceipt.provider_interactions id (memoryChannel (p := p)).toRaw (by
      intro same
      exact Bool.noConfusion (congrArg (fun channel => channel.name == "SP1Memory") same))]
  apply List.mem_map.mpr
  refine ⟨i.toRaw, ?_, pulled⟩
  simp only [Component.interactionsWith_eq, Component.rowOperations]
  change i.toRaw ∈ (((supportedChipFor (p := p) id).circuit.main (varFromOffset _ 0)).operations
    (size (supportedChipFor (p := p) id).kind.Inputs)).interactionsWith memoryChannel.toRaw
  rw [original_memory]
  exact List.mem_map_of_mem member

/-- The private source must arise in the same row as an actual positive predecessor on the original
Memory channel. Its upper clock comes from that row's authenticated incoming State projection. -/
def FromPull (id : InstructionChipId) (table : Table (ZMod p)) (record : Readback (ZMod p)) : Prop :=
  FromPredecessor table (fun env =>
    let state := eval env ((layout (p := p) id).incoming (varFromOffset _ 0))
    (state.clk_high, state.clk_low)) record

/-- Reuse a full physical table, preserving original rows, data, generation and all fixed cells. -/
def publish (id : InstructionChipId) (table : Table (ZMod p)) (registered : table.component = ProtectedOrdinaryReceipt.component id) :
    Table (ZMod p) :=
  table.withComponent (component id) (by rw [registered]; exact width id) (by
      rw [registered]
      funext rows
      dsimp only [component, ProtectedOrdinaryReceipt.component, Component.FixedRowsMatch]
      split <;> rfl)
    (by rw [registered]; exact Receipt.many_name _ _ (fun _ _ => trivial) _)
    (by rw [registered]; rfl)

theorem publish_constraints (id : InstructionChipId) (table : Table (ZMod p))
    (registered : table.component = ProtectedOrdinaryReceipt.component id) :
    (publish id table registered).Constraints ↔ table.Constraints := by
  apply Table.withComponent_constraints
  · rw [registered, constraints]
  · rw [registered, lookups]

theorem publish_authenticates (id : InstructionChipId) (table : Table (ZMod p))
    (registered : table.component = ProtectedOrdinaryReceipt.component id) :
    (publish id table registered).Authenticates readbackChannel (FromPull id table) := by
  intro physical member interaction live active
  change interaction ∈ (component id).operations.interactionValuesWith readbackChannel.toRaw (table.environment physical) at live
  rw [row_receipts] at live
  obtain ⟨i, seen, rfl⟩ := List.mem_map.mp live
  refine ⟨_, rfl, physical, member, _, _, active.1, ?_, rfl⟩
  rw [registered]
  exact protected_pull id (table.environment physical) i seen

theorem publish_interactions (id : InstructionChipId) (table : Table (ZMod p))
    (registered : table.component = ProtectedOrdinaryReceipt.component id)
    (channel : RawChannel (ZMod p)) (other : channel ≠ readbackChannel.toRaw) :
    (publish id table registered).interactionsWith channel = table.interactionsWith channel := by
  apply Table.withComponent_interactions
  rw [registered]
  exact interactions id channel other

/-- Padding and duplicated pull sites have their original number of physical ledger occurrences. -/
theorem publication_count (id : InstructionChipId) (table : Table (ZMod p))
    (registered : table.component = ProtectedOrdinaryReceipt.component id) :
    ((publish id table registered).interactionsWith readbackChannel.toRaw).length =
      table.length * accessCount (p := p) id := by
  simp only [publish, Table.interactionsWith, Table.withComponent, Table.environment, row_receipts, Table.length]
  induction table.table with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, Nat.succ_mul] at ih ⊢
    rw [ih]
    exact Nat.add_comm _ _

end SP1Clean.WriteProbe.OrdinarySources
