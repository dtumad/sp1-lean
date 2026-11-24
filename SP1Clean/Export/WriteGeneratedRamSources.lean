import SP1Clean.Proofs.Completeness.MemoryInstructionRows
import SP1Clean.Export.WriteGeneratedRegisterSources

/-! # Original RAM receipts from generated loads and stores

The released Memory access reads its address from the witnessed AddressOperation output.
The bundled circuit specification identifies all three aligned limbs and the actual input
row provides the full previous timestamp and displaced word.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory Soundness.Target

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

private def ramEntry (e : MemoryEvent) : MemRecordEntry := ⟨e.addr / 8 * 8, e.prevMem, e.prevTsMem, true⟩

private theorem aligned_fields {input : AddressOperation.Inputs F} {cols : Circuits.Types.AddressOperation F}
    {addr : ℕ} (spec : AddressOperation.Spec input cols) (raw : (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 = addr) :
    AddressOperation.alignedValue input cols = Address.ofNat (addr / 8 * 8) := by
  have hz := spec.1.trans raw
  obtain ⟨low, middle, high⟩ := AddressOperation.limbBounds_of_spec spec
  have offset := spec.2.2.2.2.2.2.1.trans (congrArg (· % 8) raw)
  have offsetCast := congrArg (Nat.cast (R := F)) offset
  push_cast at offsetCast
  simp only [ZMod.natCast_zmod_val] at offsetCast
  have rem : addr % 8 ≤ cols.addr_operation.value[0].val := by omega
  apply Vector.ext
  intro i hi
  interval_cases i
  · change cols.addr_operation.value[0] - 4 * input.offset_bit2 - 2 * input.offset_bit1 - input.offset_bit0 = (((addr / 8 * 8) % 2 ^ 16 : ℕ) : F)
    rw [show addr / 8 * 8 % 2 ^ 16 = cols.addr_operation.value[0].val - addr % 8 by omega, Nat.cast_sub rem, ZMod.natCast_zmod_val, ← offsetCast]
    ring
  · change cols.addr_operation.value[1] = (((addr / 8 * 8 / 2 ^ 16) % 2 ^ 16 : ℕ) : F)
    rw [show addr / 8 * 8 / 2 ^ 16 % 2 ^ 16 = cols.addr_operation.value[1].val by omega, ZMod.natCast_zmod_val]
  · change cols.addr_operation.value[2] = (((addr / 8 * 8 / 2 ^ 32) % 2 ^ 16 : ℕ) : F)
    rw [show addr / 8 * 8 / 2 ^ 32 % 2 ^ 16 = cols.addr_operation.value[2].val by omega, ZMod.natCast_zmod_val]

private theorem ramPrior_of_spec (e : MemoryEvent) (fits : e.addr < 2 ^ 48)
    (access : Trace.RamAccessView F) {input : AddressOperation.Inputs F} {cols : Circuits.Types.AddressOperation F}
    (spec : AddressOperation.Spec input cols) (aligned : access.address = AddressOperation.alignedValue input cols)
    (base : input.b = wordOfNat e.b) (imm : input.cc = wordOfNat e.imm)
    (high : access.prevHigh = ((e.prevTsMem >>> 24 : ℕ) : F))
    (low : access.prevLow = ((e.prevTsMem % 2 ^ 24 : ℕ) : F)) (word : access.priorValue = wordOfNat e.prevMem) :
    ramPriorMessage access = (ramEntry e).toMemoryMsg := by
  have addr : (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 = e.addr := by
    rw [base, imm, wordOfNat_toNat, wordOfNat_toNat]
    unfold MemoryEvent.addr at fits ⊢
    omega
  have exactAddress := aligned.trans (aligned_fields spec addr)
  simp only [ramPriorMessage, exactAddress, high, low, word, Nat.shiftRight_eq_div_pow, ramEntry, MemRecordEntry.toMemoryMsg]
  rfl

private theorem generated_ram_payload (id : InstructionChipId) (e : id.Event) {ram : MemoryEvent}
    (family : RoutedEvent.memoryEvent? ⟨id, e⟩ = some ram) (valid : id.Valid e) (cols : (supportedChipFor id).kind.Cols F)
    (data : ProverData F) (spec : (installed id).circuit.Spec (InstalledInstructionTables.activeInput id e) cols data)
    (active : ((supportedChipFor id).kind.view (InstalledInstructionTables.activeInput id e) cols).is_real = 1) :
    ramPriorMessage (((supportedChipFor id).kind.ramAccess (InstalledInstructionTables.activeInput id e) cols).getD zeroRamAccess) =
      (ramEntry ram).toMemoryMsg := by
  cases id <;> simp only [RoutedEvent.memoryEvent?, reduceCtorEq] at family
  all_goals
    have same : e = ram := Option.some.inj family
    subst ram
  case loadByte =>
    have original : LoadByteChip.Spec e.toLoadByteInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case loadHalf =>
    have original : LoadHalfChip.Spec e.toLoadHalfInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case loadWord =>
    have original : LoadWordChip.Spec e.toLoadWordInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case loadDouble =>
    have original : LoadDoubleChip.Spec e.toLoadDoubleInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case loadX0 =>
    have original : LoadX0Chip.Spec e.toLoadX0Inputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case storeByte =>
    have original : StoreByteChip.Spec e.toStoreByteInputs cols data := spec
    exact ramPrior_of_spec e valid.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case storeHalf =>
    have original : StoreHalfChip.Spec e.toStoreHalfInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case storeWord =>
    have original : StoreWordChip.Spec e.toStoreWordInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl
  case storeDouble =>
    have original : StoreDoubleChip.Spec e.toStoreDoubleInputs cols data := spec
    exact ramPrior_of_spec e valid.1.addr_lt _ (original.1.2.2.2 active) rfl rfl rfl rfl rfl rfl

private theorem ram_consumed (id : InstructionChipId) (e : id.Event) {ram : MemoryEvent} (family : RoutedEvent.memoryEvent? ⟨id, e⟩ = some ram)
    (cells : Array F) (data : ProverData F)
    (real : ((supportedChipFor id).decodeRow data cells).is_real = 1) :
    let row : DecodedInstructionRow SP1Prime := ⟨supportedChipFor id, cells⟩
    ramPriorMessage (decodedRamAccess row data) ∈ row.consumedMemoryMessages data := by
  intro row
  cases id <;> simp only [RoutedEvent.memoryEvent?, reduceCtorEq] at family
  case loadByte => rw [consumedMemoryMessages_eq_of_loadShape loadByteChip_loadMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case loadHalf => rw [consumedMemoryMessages_eq_of_loadShape loadHalfChip_loadMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case loadWord => rw [consumedMemoryMessages_eq_of_loadShape loadWordChip_loadMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case loadDouble => rw [consumedMemoryMessages_eq_of_loadShape loadDoubleChip_loadMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case loadX0 => rw [consumedMemoryMessages_eq_of_immutableRamShape loadX0Chip_immutableRamMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case storeByte => rw [consumedMemoryMessages_eq_of_immutableRamShape storeByteChip_immutableRamMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case storeHalf => rw [consumedMemoryMessages_eq_of_immutableRamShape storeHalfChip_immutableRamMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case storeWord => rw [consumedMemoryMessages_eq_of_immutableRamShape storeWordChip_immutableRamMemoryInteractionShape row data rfl real]; exact List.mem_cons_self
  case storeDouble => rw [consumedMemoryMessages_eq_of_immutableRamShape storeDoubleChip_immutableRamMemoryInteractionShape row data rfl real]; exact List.mem_cons_self

private theorem generated_ram_entry (id : InstructionChipId) (events : List id.Event) {e : id.Event}
    (used : e ∈ events) (valid : id.Valid e) {ram : MemoryEvent} (family : RoutedEvent.memoryEvent? ⟨id, e⟩ = some ram)
    (data evaluation : ProverData F) (hint : ProverHint F) (fit) :
    let base := (RoutedEvent.mk id e).clock
    ∃ cells ∈ (InstalledInstructionTables.table id events data hint fit).table,
      (1, AccessSupply.atClock (((base / 2 ^ 24 : ℕ) : F), ((base % 2 ^ 24 : ℕ) : F)) (ramEntry ram).toMemoryMsg) ∈
        rowRecords (.ordinary id) (Environment.fromArray cells evaluation) := by
  intro base
  let c := installed id
  let original := InstalledInstructionTables.table id events data hint fit
  let input := InstalledInstructionTables.activeInput id e
  let cells := c.buildRow input original.data hint
  let env := Environment.fromArray cells evaluation
  let row : DecodedInstructionRow SP1Prime := ⟨supportedChipFor id, cells⟩
  let cols := (supportedChipFor id).table.rowOutput env
  have actual : c.rowInput env = input := c.rowInput_buildRow _ _ _ _
  have present : cells ∈ original.table := by
    apply List.mem_map_of_mem (f := fun x => c.buildRow x original.data hint)
    exact List.mem_append_left _ (List.mem_map_of_mem used)
  have spec := InstalledInstructionTables.active_memory_spec id e valid family original.data evaluation hint
  have active := InstalledInstructionTables.active_is_real id e valid original.data evaluation hint
  have activeInput : ((supportedChipFor id).kind.view input cols).is_real = 1 := by
    change ((supportedChipFor id).kind.view (c.rowInput env) cols).is_real = 1 at active
    rwa [actual] at active
  have payload := generated_ram_payload id e family valid cols original.data spec activeInput
  have inLedger := ram_consumed id e family cells evaluation active
  have same : decodedRamAccess row evaluation =
      (((supportedChipFor id).kind.ramAccess input cols).getD zeroRamAccess) := by
    change (((supportedChipFor id).kind.ramAccess (c.rowInput env) cols).getD zeroRamAccess) = _
    rw [actual]
  change ramPriorMessage (decodedRamAccess row evaluation) ∈ row.consumedMemoryMessages evaluation at inLedger
  rw [same, payload] at inLedger
  exact ⟨cells, present, ordinary_receipt_at_event id e evaluation cells actual inLedger⟩

private theorem iType_prior_small (e : ITypeEvent) (a : e.opA < 32) (b : e.opB < 32) :
    ∀ r ∈ e.predecessors, r.addr < 32 := by
  simp [ITypeEvent.predecessors, a, b]

private theorem rType_prior_small (e : RTypeEvent) (a : e.opA < 32) (b : e.opB < 32) (c : e.opC < 32) :
    ∀ r ∈ e.predecessors, r.addr < 32 := by
  simp [RTypeEvent.predecessors, a, b, c]

private theorem alu_prior_small (e : ALUTypeEvent) (a : e.opA < 32) (b : e.opB < 32) (c : e.immC = 0 → e.opC < 32) :
    ∀ r ∈ e.predecessors, r.addr < 32 := by
  by_cases immediate : e.immC = 0 <;> simp [ALUTypeEvent.predecessors, immediate, c, a, b]

private theorem ram_prior_large (e : MemoryEvent) (a : e.opA < 32) (b : e.opB < 32) {r : MemRecordEntry}
    (used : r ∈ e.predecessors) (large : 32 ≤ r.addr) : r = ramEntry e := by
  rcases List.mem_cons.mp used with prior | reg
  · exact prior
  · exact False.elim ((iType_prior_small e.toITypeEvent a b _ reg).not_ge large)

private theorem ram_origin (id : InstructionChipId) (e : id.Event) (valid : id.Valid e) {r : MemRecordEntry}
    (used : r ∈ (RoutedEvent.mk id e).predecessors) (large : 32 ≤ r.addr) :
    ∃ memory, RoutedEvent.memoryEvent? ⟨id, e⟩ = some memory ∧ r = ramEntry memory := by
  cases id with
  | add | sub | subw => exact False.elim ((rType_prior_small _ valid.opA_lt valid.opB_lt valid.opC_lt _ used).not_ge large)
  | mul | divRem => exact False.elim ((rType_prior_small _ valid.1.opA_lt valid.1.opB_lt valid.1.opC_lt _ used).not_ge large)
  | addi => exact False.elim ((iType_prior_small _ valid.opA_lt valid.opB_lt _ used).not_ge large)
  | jalr | branch => exact False.elim ((iType_prior_small _ valid.1.opA_lt valid.1.opB_lt _ used).not_ge large)
  | jal | uType =>
    obtain rfl := List.mem_singleton.mp used
    exact False.elim (valid.1.opA_lt.not_ge large)
  | addw => exact False.elim ((alu_prior_small _ valid.opA_lt valid.opB_lt valid.opC_reg _ used).not_ge large)
  | bitwise | lt | shiftLeft | shiftRight =>
    exact False.elim ((alu_prior_small _ valid.1.opA_lt valid.1.opB_lt valid.1.opC_reg _ used).not_ge large)
  | aluX0 =>
    exact False.elim ((alu_prior_small _ (by rw [valid.opA_eq_zero]; decide) valid.opB_lt valid.opC_reg _ used).not_ge large)
  | loadByte | loadHalf | loadWord | loadDouble =>
    exact ⟨e, rfl, ram_prior_large _ valid.1.toITypeWellFormed.opA_lt valid.1.toITypeWellFormed.opB_lt used large⟩
  | loadX0 =>
    exact ⟨e, rfl, ram_prior_large _ (by rw [valid.1.opA_eq_zero]; decide) valid.1.opB_lt used large⟩
  | storeByte => exact ⟨e, rfl, ram_prior_large _ valid.opA_lt valid.opB_lt used large⟩
  | storeHalf | storeWord | storeDouble => exact ⟨e, rfl, ram_prior_large _ valid.1.opA_lt valid.1.opB_lt used large⟩

/-- Every physically valid operand on the canonical mixed Sail tape, including a witnessed
load or store address, supplies its full positive receipt from the selected original table. -/
theorem generated_ordinary {program : GuestProgram} {located : LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {base : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (made : compileInstructionEvent? view frontier base = some result) (phase : activeClockPhase base)
    {touch : StampedTouch} (used : touch ∈ result.stamped) (legal : touch.touch.loc.CanonicalAddress)
    (events : List result.routed.id.Event) (bucket : result.routed.event ∈ events) (valid : result.routed.id.Valid result.routed.event)
    (data evaluation : ProverData F) (hint : ProverHint F) (fit) :
    ∃ cells ∈ (InstalledInstructionTables.table result.routed.id events data hint fit).table,
      (1, compiledReadback base (.ofStamped base touch)) ∈ rowRecords (.ordinary result.routed.id) (Environment.fromArray cells evaluation) := by
  cases loc : touch.touch.loc with
  | reg i => exact generated_ordinary_register projected made phase used loc events bucket valid data evaluation hint fit
  | ram cell =>
    have large : 32 ≤ (operandPredecessor touch).addr := by
      rw [loc] at legal
      change 32 ≤ touch.touch.loc.busAddress
      rw [loc]
      exact legal.1
    have entry : operandPredecessor touch ∈ result.routed.predecessors :=
      (compileInstructionEvent?_predecessors projected made) ▸ List.mem_map_of_mem used
    obtain ⟨ram, family, prior⟩ := ram_origin result.routed.id result.routed.event valid entry large
    have physical := generated_ram_entry result.routed.id events bucket valid family data evaluation hint fit
    have time := (compileInstructionEvent?_coordinates made).1
    rwa [show (RoutedEvent.mk _ _).clock = base from time, ← prior] at physical

end SP1Clean.Export.WriteSourceRegistry
