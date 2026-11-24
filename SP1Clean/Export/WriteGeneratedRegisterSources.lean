import SP1Clean.Export.WriteGeneratedHostSources
import SP1Clean.Proofs.Completeness.MixedInstructionTables
import SP1Clean.Soundness.WriteRegisterPredecessors

/-! # Original register receipts from compiled ordinary instructions

The registered circuit view recovers the exact compiler inputs for every ordinary instruction.
A genuine scheduled register access recovers its pre-refresh timestamp from SP1's compressed
timestamp columns, including register aliases at different offsets of the same instruction.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory Soundness.Target

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

private def eventAdapter : (id : InstructionChipId) → id.Event → Trace.AdapterView F
  | .add | .sub | .subw | .mul | .divRem => fun e => (rTypeReaderCols e).toAdapterView
  | .addi | .jalr | .branch => fun e => (iTypeReaderCols e).toAdapterView
  | .addw | .bitwise | .lt | .shiftLeft | .shiftRight | .aluX0 => fun e => (aluTypeReaderCols e).toAdapterView
  | .jal | .uType => fun e => (jTypeReaderCols e).toAdapterView
  | .loadByte | .loadHalf | .loadWord | .loadDouble | .loadX0 | .storeByte | .storeHalf | .storeWord | .storeDouble =>
    fun e => (iTypeReaderCols e.toITypeEvent).toAdapterView

/-- The normalized view of a register-only instruction reads its state and adapter from the
evaluated original input. The chip's existing projection equations keep its circuit folded. -/
local macro "registerView " chip:ident : tactic => do
  let name := chip.getId.toString
  let input := Lean.mkIdent ((Lean.Name.mkSimple (name.capitalize ++ "Chip")) ++ `Inputs)
  let view := Lean.mkIdent (.mkSimple (name ++ "ViewOf"))
  let state := Lean.mkIdent (.mkSimple (name ++ "ViewOf_state"))
  let adapter := Lean.mkIdent (.mkSimple (name ++ "ViewOf_adapter"))
  let decoded := Lean.mkIdent `decoded
  `(tactic| (
    change valueFromOffset $input 0 _ = _ at $decoded:ident
    change ($view _).state = _ ∧ ($view _).adapter = _
    simp only [$state:ident, $adapter:ident, eval_varFromOffset_valueFromOffset, $decoded:ident]
    exact ⟨rfl, rfl⟩))

/-- Each RAM row's state and register reader project directly from the committed inputs. -/
local macro "memoryView " input:term : tactic => do
  let decoded := Lean.mkIdent `decoded
  `(tactic| (
    change (valueFromOffset $input 0 _).state = _ ∧ (valueFromOffset $input 0 _).adapter.toAdapterView = _
    change valueFromOffset $input 0 _ = _ at $decoded:ident
    rw [$decoded:ident]
    exact ⟨rfl, rfl⟩))

private theorem generated_view (id : InstructionChipId) (event : id.Event) (data : ProverData F) (cells : Array F)
    (decoded : (installed id).rowInput (Environment.fromArray cells data) = InstalledInstructionTables.activeInput id event) :
    let view := ((supportedChipFor id).decodeRow data cells).view
    let routed : RoutedEvent := ⟨id, event⟩
    view.state = cpuStateCols routed.clock routed.pc ∧ view.adapter = eventAdapter id event := by
  dsimp only
  cases id with
  | add => registerView add
  | addi => registerView addi
  | addw => registerView addw
  | sub => registerView sub
  | subw => registerView subw
  | bitwise => registerView bitwise
  | lt => registerView lt
  | shiftLeft => registerView shiftLeft
  | shiftRight => registerView shiftRight
  | jal => registerView jal
  | jalr => registerView jalr
  | branch => registerView branch
  | uType => registerView uType
  | mul => registerView mul
  | divRem => registerView divRem
  | aluX0 => registerView aluX0
  | loadByte => memoryView LoadByteChip.Inputs
  | loadHalf => memoryView LoadHalfChip.Inputs
  | loadWord => memoryView LoadWordChip.Inputs
  | loadDouble => memoryView LoadDoubleChip.Inputs
  | loadX0 => memoryView LoadX0Chip.Inputs
  | storeByte => memoryView StoreByteChip.Inputs
  | storeHalf => memoryView StoreHalfChip.Inputs
  | storeWord => memoryView StoreWordChip.Inputs
  | storeDouble => memoryView StoreDoubleChip.Inputs

private def packedRegister (base offset : ℕ) (r : MemRecordEntry) : MemoryMsg F :=
  ⟨((base / 2 ^ 24 : ℕ) : F), (prevLowOf r.clk (base + offset) : F), (r.addr : F), 0, 0, wordOfNat r.value⟩

private def RegisterRows (view : Trace.RowView F) (base : ℕ) (entries : List MemRecordEntry) : Prop :=
  ∀ r ∈ entries, r.addr < 32 → ∃ offset ≤ 4, packedRegister base offset r ∈ OrdinarySources.registerPriors view

private theorem registerA (view : Trace.RowView F) :
    rtypePriorMessage view view.adapter.op_a view.adapter.op_a_memory ∈ OrdinarySources.registerPriors view := by
  simp [OrdinarySources.registerPriors]

private theorem registerB (view : Trace.RowView F) (reg : view.adapter.imm_b = 0) :
    rtypePriorMessage view view.adapter.op_b[0] view.adapter.op_b_memory ∈ OrdinarySources.registerPriors view := by
  simp [OrdinarySources.registerPriors, reg]

private theorem registerC (view : Trace.RowView F) (reg : view.adapter.imm_c = 0) :
    rtypePriorMessage view view.adapter.op_c[0] view.adapter.op_c_memory ∈ OrdinarySources.registerPriors view := by
  simp [OrdinarySources.registerPriors, reg]

private theorem rType_registerRows (e : RTypeEvent) (view : Trace.RowView F)
    (state : view.state = cpuStateCols e.clk e.pc) (adapter : view.adapter = (rTypeReaderCols e).toAdapterView) :
    RegisterRows view e.clk e.predecessors := by
  intro r used small
  simp only [RTypeEvent.predecessors, List.mem_cons, List.not_mem_nil, or_false] at used
  rcases used with rfl | rfl | rfl
  · refine ⟨2, by decide, ?_⟩
    have prior := registerC view (adapter ▸ rfl)
    simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
    exact prior
  · refine ⟨3, by decide, ?_⟩
    have prior := registerB view (adapter ▸ rfl)
    simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
    exact prior
  · refine ⟨4, by decide, ?_⟩
    have prior := registerA view
    simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
    exact prior

private theorem iType_registerRows (e : ITypeEvent) (view : Trace.RowView F)
    (state : view.state = cpuStateCols e.clk e.pc) (adapter : view.adapter = (iTypeReaderCols e).toAdapterView) :
    RegisterRows view e.clk e.predecessors := by
  intro r used small
  simp only [ITypeEvent.predecessors, List.mem_cons, List.not_mem_nil, or_false] at used
  rcases used with rfl | rfl
  · refine ⟨3, by decide, ?_⟩
    have prior := registerB view (adapter ▸ rfl)
    simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
    exact prior
  · refine ⟨4, by decide, ?_⟩
    have prior := registerA view
    simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
    exact prior

private theorem jType_registerRows (e : JTypeEvent) (view : Trace.RowView F)
    (state : view.state = cpuStateCols e.clk e.pc) (adapter : view.adapter = (jTypeReaderCols e).toAdapterView) :
    RegisterRows view e.clk e.predecessors := by
  intro r used small
  obtain rfl := List.mem_singleton.mp used
  refine ⟨4, by decide, ?_⟩
  have prior := registerA view
  simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
  exact prior

private theorem alu_registerRows (e : ALUTypeEvent) (view : Trace.RowView F)
    (state : view.state = cpuStateCols e.clk e.pc) (adapter : view.adapter = (aluTypeReaderCols e).toAdapterView) :
    RegisterRows view e.clk e.predecessors := by
  intro r used small
  rw [ALUTypeEvent.predecessors, List.mem_append] at used
  rcases used with h | h
  · split at h
    · rename_i reg
      obtain rfl := List.mem_singleton.mp h
      refine ⟨2, by decide, ?_⟩
      have gate : view.adapter.imm_c = 0 := by rw [adapter]; change (e.immC : F) = 0; simp [reg]
      have prior := registerC view gate
      change e.opC < 32 at small
      have idx : (wordOfNat (p := SP1Prime) e.opC)[0] = (e.opC : F) := by
        change ((e.opC % 2 ^ 16 : ℕ) : F) = _
        rw [Nat.mod_eq_of_lt (by omega)]
      simp only [rtypePriorMessage, state, adapter, Circuits.Types.ALUTypeReader.toAdapterView,
        aluTypeReaderCols_op_c, aluTypeReaderCols_op_c_memory, aluTypeOpCCols_of_reg reg, idx,
        packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
      exact prior
    · contradiction
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine ⟨3, by decide, ?_⟩
      have prior := registerB view (adapter ▸ rfl)
      simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
      exact prior
    · refine ⟨4, by decide, ?_⟩
      have prior := registerA view
      simp only [rtypePriorMessage, state, adapter, packedRegister, cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow] at prior ⊢
      exact prior

private theorem memory_registerRows (e : MemoryEvent) (view : Trace.RowView F)
    (state : view.state = cpuStateCols e.clk e.pc) (adapter : view.adapter = (iTypeReaderCols e.toITypeEvent).toAdapterView)
    (legal : 2 ^ 16 ≤ e.addr) : RegisterRows view e.clk e.predecessors := by
  intro r used small
  rcases List.mem_cons.mp used with rfl | rest
  · change e.addr / 8 * 8 < 32 at small
    omega
  · exact iType_registerRows e.toITypeEvent view state adapter _ rest small

private theorem event_registerRows (id : InstructionChipId) (event : id.Event) (valid : id.Valid event)
    (view : Trace.RowView F) (state : view.state = cpuStateCols (RoutedEvent.mk id event).clock (RoutedEvent.mk id event).pc)
    (adapter : view.adapter = eventAdapter id event) :
    RegisterRows view (RoutedEvent.mk id event).clock (RoutedEvent.mk id event).predecessors := by
  cases id with
  | add | sub | subw | mul | divRem => exact rType_registerRows _ _ state adapter
  | addi | jalr | branch => exact iType_registerRows _ _ state adapter
  | addw | bitwise | lt | shiftLeft | shiftRight | aluX0 => exact alu_registerRows _ _ state adapter
  | jal | uType => exact jType_registerRows _ _ state adapter
  | loadByte | loadHalf | loadWord | loadDouble | loadX0 | storeHalf | storeWord | storeDouble =>
    exact memory_registerRows _ _ state adapter valid.1.addr_ge
  | storeByte => exact memory_registerRows _ _ state adapter valid.addr_ge

private theorem event_imm (id : InstructionChipId) (e : id.Event) (valid : id.Valid e) :
    (eventAdapter id e).imm_c = 0 ∨ (eventAdapter id e).imm_c = 1 := by
  cases id <;> try first | exact Or.inl rfl | exact Or.inr rfl
  all_goals
    change (e.immC : F) = 0 ∨ (e.immC : F) = 1
    have bit : e.immC = 0 ∨ e.immC = 1 := by first | exact valid.immC_bool | exact valid.1.immC_bool
    rcases bit with h | h <;> simp [h]

private theorem packedRegister_canonical {base offset : ℕ} (r : MemRecordEntry)
    (small : r.addr < 32) (window : r.clk / 2 ^ 24 = base / 2 ^ 24) (phase : activeClockPhase base) (delta : offset ≤ 4) :
    packedRegister base offset r = r.toMemoryMsg := by
  have inside := phase.window
  change base % 2 ^ 24 + 4 < 2 ^ 24 at inside
  have later : (base + offset) / 2 ^ 24 = base / 2 ^ 24 := by omega
  simp only [packedRegister, MemRecordEntry.toMemoryMsg, prevLowOf, Nat.shiftRight_eq_div_pow, window, later, ↓reduceIte,
    Nat.mod_eq_of_lt (show r.addr < 2 ^ 16 by omega), Nat.div_eq_of_lt (show r.addr < 2 ^ 16 by omega),
    Nat.div_eq_of_lt (show r.addr < 2 ^ 32 by omega), Nat.zero_mod, Nat.cast_zero]

private theorem generated_clock (view : Trace.RowView F) (base pc : ℕ) (state : view.state = cpuStateCols base pc) :
    let incoming := statePullOfView view
    (incoming.clk_high, incoming.clk_low) = (((base / 2 ^ 24 : ℕ) : F), ((base % 2 ^ 24 : ℕ) : F)) := by
  dsimp only [statePullOfView, stateAccess]
  rw [state, cpuStateCols_clk_high, cpuStateCols_clk_0_16, cpuStateCols_clk_16_24, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  congr 1
  exact (by exact_mod_cast congrArg (Nat.cast (R := F)) (show base % 2 ^ 16 + base / 2 ^ 16 % 256 * 65536 = base % 2 ^ 24 by omega))

/-- A genuine Memory predecessor of a built ordinary instruction publishes a private receipt
at the canonical clock carried by the original executor event. -/
theorem ordinary_receipt_at_event (id : InstructionChipId) (e : id.Event) (data : ProverData F) (cells : Array F)
    (decoded : (installed id).rowInput (Environment.fromArray cells data) = InstalledInstructionTables.activeInput id e)
    {prior : MemoryMsg F} (consumed : prior ∈ (⟨supportedChipFor id, cells⟩ : DecodedInstructionRow SP1Prime).consumedMemoryMessages data) :
    let base := (RoutedEvent.mk id e).clock
    (1, AccessSupply.atClock (((base / 2 ^ 24 : ℕ) : F), ((base % 2 ^ 24 : ℕ) : F)) prior) ∈
      rowRecords (.ordinary id) (Environment.fromArray cells data) := by
  have clock := generated_clock _ _ _ (generated_view id e data cells decoded).1
  have receipt := ordinary_row_predecessor id data cells consumed
  change (1, AccessSupply.atClock (_, _) prior) ∈ _ at receipt
  dsimp only at clock ⊢
  rw [← clock]
  exact receipt

private theorem generated_register_entry (id : InstructionChipId) (events : List id.Event)
    {e : id.Event} (used : e ∈ events) (valid : id.Valid e) {r : MemRecordEntry}
    (entry : r ∈ (RoutedEvent.mk id e).predecessors) (small : r.addr < 32)
    (window : r.clk / 2 ^ 24 = (RoutedEvent.mk id e).clock / 2 ^ 24) (phase : activeClockPhase (RoutedEvent.mk id e).clock)
    (data evaluation : ProverData F) (hint : ProverHint F) (fit) :
    let base := (RoutedEvent.mk id e).clock
    ∃ cells ∈ (InstalledInstructionTables.table id events data hint fit).table,
      (1, AccessSupply.atClock (((base / 2 ^ 24 : ℕ) : F), ((base % 2 ^ 24 : ℕ) : F)) r.toMemoryMsg) ∈
        rowRecords (.ordinary id) (Environment.fromArray cells evaluation) := by
  intro base
  let original := InstalledInstructionTables.table id events data hint fit
  let input := InstalledInstructionTables.activeInput id e
  let c := installed id
  let cells := c.buildRow input original.data hint
  have inTable : cells ∈ original.table := by
    apply List.mem_map_of_mem (f := fun x => c.buildRow x original.data hint)
    exact List.mem_append_left _ (List.mem_map_of_mem used)
  let row : DecodedInstructionRow SP1Prime := ⟨supportedChipFor id, cells⟩
  let view := (row.toChipRow evaluation).view
  have checked : row.chip.table.operations.ConstraintsHold (row.environment evaluation) := by
    have old := (c.buildRow_constraintsHold input original.data hint (InstalledInstructionTables.activeInput_valid id e valid _ _)).1
    have atData : c.operations.ConstraintsHold (Environment.fromArray cells evaluation) :=
      c.constraintsHold_setData (by rw [ProtectedOrdinaryReceipt.lookups, ProtectedOrdinaryReceipt.provider_lookups, supportedChipFor_lookups_empty]) old
    change (supportedChipFor id).table.operations.ConstraintsHold (Environment.fromArray cells evaluation)
    simpa only [c, Operations.ConstraintsHold, ProtectedOrdinaryReceipt.constraints, ProtectedOrdinaryReceipt.provider_constraints,
      ProtectedOrdinaryReceipt.lookups, ProtectedOrdinaryReceipt.provider_lookups] using atData
  obtain ⟨state, adapter⟩ := generated_view id e evaluation cells (c.rowInput_buildRow input original.data evaluation hint)
  have sameState : view.state = cpuStateCols base (RoutedEvent.mk id e).pc := state
  have sameAdapter : view.adapter = eventAdapter id e := adapter
  obtain ⟨offset, delta, present⟩ := event_registerRows id e valid view sameState sameAdapter r entry small
  rw [packedRegister_canonical r small window phase delta] at present
  have consumed := OrdinarySources.registerPriors_consumed id row evaluation rfl checked
    (InstalledInstructionTables.active_is_real id e valid original.data evaluation hint) (sameAdapter ▸ event_imm id e valid) _ present
  exact ⟨cells, inTable, ordinary_receipt_at_event id e evaluation cells (c.rowInput_buildRow input original.data evaluation hint) consumed⟩

/-- Every register predecessor of a compiled ordinary instruction occurs with unit weight in
that instruction's original built table, with its true previous high window and incoming CPU clock. -/
theorem generated_ordinary_register {program : GuestProgram} {located : LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {base : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (made : compileInstructionEvent? view frontier base = some result) (phase : activeClockPhase base)
    {touch : StampedTouch} (used : touch ∈ result.stamped) {index : BitVec 5} (reg : touch.touch.loc = .reg index)
    (events : List result.routed.id.Event) (bucket : result.routed.event ∈ events) (valid : result.routed.id.Valid result.routed.event)
    (data evaluation : ProverData F) (hint : ProverHint F) (fit) :
    ∃ cells ∈ (InstalledInstructionTables.table result.routed.id events data hint fit).table,
      (1, compiledReadback base (.ofStamped base touch)) ∈ rowRecords (.ordinary result.routed.id) (Environment.fromArray cells evaluation) := by
  have scheduled := compileInstructionEvent?_schedule made
  have stamped : touch ∈ (scheduleAccessPlan frontier base result.plan).stampedTouches := by
    simpa only [CompiledInstructionEvent.stamped, scheduled] using used
  have planned : touch.touch ∈ result.plan := (compileInstructionEvent?_stamped_touches made) ▸ List.mem_map_of_mem used
  have kind := (instructionAccessPlan_wellFormed (compileInstructionEvent?_accessPlan_generated projected made)).locKind _ planned
  have role : touch.touch.slot ≠ .ram := by intro h; simp [h, reg, AccessSlot.Accepts] at kind
  have prior := (scheduleAccessPlan_register_window phase.window stamped reg role).1
  have small : (operandPredecessor touch).addr < 32 := by
    simpa only [operandPredecessor, reg, MemLoc.busAddress] using index.isLt
  have entry : operandPredecessor touch ∈ result.routed.predecessors :=
    (compileInstructionEvent?_predecessors projected made) ▸ List.mem_map_of_mem used
  have time := (compileInstructionEvent?_coordinates made).1
  have result := generated_register_entry result.routed.id events bucket valid entry small
    (by rw [show (RoutedEvent.mk result.routed.id result.routed.event).clock = base from time]; exact prior)
    (time ▸ phase) data evaluation hint fit
  rwa [show (RoutedEvent.mk _ _).clock = base from time] at result

end SP1Clean.Export.WriteSourceRegistry
