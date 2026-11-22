import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Soundness.ProtectedOrdinaryReceipt
import SP1Clean.Math.SP1Field
import ToClean.Air.DemandPadding

/-! # Constructing the installed ordinary instruction tables

Each chronological bucket supplies its active rows in order. The suffix uses the actual
generation mode on the protected, receipt-publishing component, including DivRem's nonzero
denominator. Heights and receipt counts include all demand padding.
-/

namespace SP1Clean.TraceGen.InstalledInstructionTables

open Air.Flat Circuit WitnessGeneration Soundness

local notation "Fp" => ZMod SP1Prime
local notation "installed" => ProtectedOrdinaryReceipt.component (p := SP1Prime)

/-- Pack one semantic event using the registered instruction family's input format. -/
def activeInput : (id : InstructionChipId) → id.Event → (installed id).Input Fp
  | .add => RTypeEvent.toAddInputs
  | .addi => ITypeEvent.toAddiInputs
  | .addw => ALUTypeEvent.toAddwInputs
  | .sub => RTypeEvent.toSubInputs
  | .subw => RTypeEvent.toSubwInputs
  | .bitwise => ALUTypeEvent.toBitwiseInputs
  | .lt => ALUTypeEvent.toLtInputs
  | .shiftLeft => ALUTypeEvent.toShiftLeftInputs
  | .shiftRight => ALUTypeEvent.toShiftRightInputs
  | .jal => JTypeEvent.toJalInputs
  | .jalr => ITypeEvent.toJalrInputs
  | .branch => ITypeEvent.toBranchInputs
  | .uType => JTypeEvent.toUTypeInputs
  | .loadByte => MemoryEvent.toLoadByteInputs
  | .loadHalf => MemoryEvent.toLoadHalfInputs
  | .loadWord => MemoryEvent.toLoadWordInputs
  | .loadDouble => MemoryEvent.toLoadDoubleInputs
  | .loadX0 => MemoryEvent.toLoadX0Inputs
  | .storeByte => MemoryEvent.toStoreByteInputs
  | .storeHalf => MemoryEvent.toStoreHalfInputs
  | .storeWord => MemoryEvent.toStoreWordInputs
  | .storeDouble => MemoryEvent.toStoreDoubleInputs
  | .mul => RTypeEvent.toMulInputs
  | .divRem => RTypeEvent.toDivRemInputs
  | .aluX0 => ALUTypeEvent.toAluX0Inputs

/-- The typed inactive input shared by the local contracts and the installed demand mode. -/
def paddingInput : (id : InstructionChipId) → (installed id).Input Fp
  | .add => addPaddingInputs
  | .addi => addiPaddingInputs
  | .addw => addwPaddingInputs
  | .sub => subPaddingInputs
  | .subw => subwPaddingInputs
  | .bitwise => bitwisePaddingInputs
  | .lt => ltPaddingInputs
  | .shiftLeft => shiftLeftPaddingInputs
  | .shiftRight => shiftRightPaddingInputs
  | .jal => jalPaddingInputs
  | .jalr => jalrPaddingInputs
  | .branch => branchPaddingInputs
  | .uType => uTypePaddingInputs
  | .loadByte => (0 : LoadByteChip.Inputs Fp)
  | .loadHalf => (0 : LoadHalfChip.Inputs Fp)
  | .loadWord => (0 : LoadWordChip.Inputs Fp)
  | .loadDouble => (0 : LoadDoubleChip.Inputs Fp)
  | .loadX0 => (0 : LoadX0Chip.Inputs Fp)
  | .storeByte => (0 : StoreByteChip.Inputs Fp)
  | .storeHalf => (0 : StoreHalfChip.Inputs Fp)
  | .storeWord => (0 : StoreWordChip.Inputs Fp)
  | .storeDouble => (0 : StoreDoubleChip.Inputs Fp)
  | .mul => mulPaddingInputs
  | .divRem => DivRemChip.paddingInputs
  | .aluX0 => aluX0PaddingInputs

/-- The physical generator and the proved local contract use literally the same packed input. -/
theorem generation_padding (id : InstructionChipId) :
    ∃ mode, (installed id).generation = .demand mode ∧ mode.padding = paddingInput id := by
  cases id <;> refine ⟨_, rfl, ?_⟩ <;>
    first | rfl | apply ProvableType.toElements_inj_iff.mp; decide +kernel

/-- Each active row satisfies the protected receipt publisher's complete prover contract. -/
theorem activeInput_valid (id : InstructionChipId) (event : id.Event) (valid : id.Valid event)
    (data : ProverData Fp) (hint : ProverHint Fp) :
    (installed id).circuit.ProverAssumptions (activeInput id event) data hint := by
  cases id with
  | add => exact AddChip.proverAssumptions_of_event valid data hint
  | addi => exact AddiChip.proverAssumptions_of_event valid data hint
  | addw => exact AddwChip.proverAssumptions_of_event valid data hint
  | sub => exact SubChip.proverAssumptions_of_event valid data hint
  | subw => exact SubwChip.proverAssumptions_of_event valid data hint
  | bitwise => exact BitwiseChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | lt => exact LtChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | shiftLeft => exact ShiftLeftChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | shiftRight => exact ShiftRightChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | jal => exact JalChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | jalr => exact JalrChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | branch => exact BranchChip.proverAssumptions_of_event valid.1 valid.2.1 valid.2.2 data hint
  | uType => exact UTypeChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | loadByte => exact LoadByteChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | loadHalf => exact LoadHalfChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | loadWord => exact LoadWordChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | loadDouble => exact LoadDoubleChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | loadX0 => exact LoadX0Chip.proverAssumptions_of_event valid.1 valid.2 data hint
  | storeByte => exact StoreByteChip.proverAssumptions_of_event valid data hint
  | storeHalf => exact StoreHalfChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | storeWord => exact StoreWordChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | storeDouble => exact StoreDoubleChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | mul => exact MulChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | divRem => exact DivRemChip.proverAssumptions_of_event valid.1 valid.2 data hint
  | aluX0 => exact AluX0Chip.proverAssumptions_of_event valid data hint

-- The memory chips expose several nested reader and range contracts. At the registered all-zero
-- input these reduce to closed bounds and field arithmetic, independent of the data and hint.
local macro "memory_padding" : tactic => `(tactic| (
  unfold Word.isU64 Readers.CPUState.Spec Readers.MemoryAccess.Spec
  first | unfold Readers.ITypeReader.Spec | unfold Readers.ITypeReaderImmutable.Spec
  unfold Readers.RegisterAccessCols.Spec Readers.RegisterAccessTimestamp.Spec
  try unfold U16MSBOperation.Spec
  unfold Word.isU64
  repeat' apply And.intro
  all_goals decide +kernel))

private theorem loadByte_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    LoadByteChip.ProverAssumptions (0 : LoadByteChip.Inputs Fp) data hint := by
  unfold LoadByteChip.ProverAssumptions
  memory_padding

private theorem loadHalf_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    LoadHalfChip.ProverAssumptions (0 : LoadHalfChip.Inputs Fp) data hint := by
  unfold LoadHalfChip.ProverAssumptions
  memory_padding

private theorem loadWord_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    LoadWordChip.ProverAssumptions (0 : LoadWordChip.Inputs Fp) data hint := by
  unfold LoadWordChip.ProverAssumptions
  memory_padding

private theorem loadDouble_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    LoadDoubleChip.ProverAssumptions (0 : LoadDoubleChip.Inputs Fp) data hint := by
  unfold LoadDoubleChip.ProverAssumptions
  memory_padding

private theorem loadX0_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    LoadX0Chip.ProverAssumptions (0 : LoadX0Chip.Inputs Fp) data hint := by
  unfold LoadX0Chip.ProverAssumptions
  memory_padding

private theorem storeByte_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    StoreByteChip.ProverAssumptions (0 : StoreByteChip.Inputs Fp) data hint := by
  unfold StoreByteChip.ProverAssumptions
  memory_padding

private theorem storeHalf_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    StoreHalfChip.ProverAssumptions (0 : StoreHalfChip.Inputs Fp) data hint := by
  unfold StoreHalfChip.ProverAssumptions
  memory_padding

private theorem storeWord_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    StoreWordChip.ProverAssumptions (0 : StoreWordChip.Inputs Fp) data hint := by
  unfold StoreWordChip.ProverAssumptions
  memory_padding

private theorem storeDouble_padding (data : ProverData Fp) (hint : ProverHint Fp) :
    StoreDoubleChip.ProverAssumptions (0 : StoreDoubleChip.Inputs Fp) data hint := by
  unfold StoreDoubleChip.ProverAssumptions
  memory_padding

/-- The registered scheduler suffix satisfies the same contract, including every memory family. -/
theorem paddingInput_valid (id : InstructionChipId) (data : ProverData Fp) (hint : ProverHint Fp) :
    (installed id).circuit.ProverAssumptions (paddingInput id) data hint := by
  cases id with
  | add => exact AddChip.proverAssumptions_padding data hint
  | addi => exact AddiChip.proverAssumptions_padding data hint
  | addw => exact AddwChip.proverAssumptions_padding data hint
  | sub => exact SubChip.proverAssumptions_padding data hint
  | subw => exact SubwChip.proverAssumptions_padding data hint
  | bitwise => exact BitwiseChip.proverAssumptions_padding data hint
  | lt => exact LtChip.proverAssumptions_padding data hint
  | shiftLeft => exact ShiftLeftChip.proverAssumptions_padding data hint
  | shiftRight => exact ShiftRightChip.proverAssumptions_padding data hint
  | jal => exact JalChip.proverAssumptions_padding data hint
  | jalr => exact JalrChip.proverAssumptions_padding data hint
  | branch => exact BranchChip.proverAssumptions_padding data hint
  | uType => exact UTypeChip.proverAssumptions_padding data hint
  | loadByte =>
    dsimp only [paddingInput]
    exact loadByte_padding data hint
  | loadHalf =>
    dsimp only [paddingInput]
    exact loadHalf_padding data hint
  | loadWord =>
    dsimp only [paddingInput]
    exact loadWord_padding data hint
  | loadDouble =>
    dsimp only [paddingInput]
    exact loadDouble_padding data hint
  | loadX0 =>
    dsimp only [paddingInput]
    exact loadX0_padding data hint
  | storeByte =>
    dsimp only [paddingInput]
    exact storeByte_padding data hint
  | storeHalf =>
    dsimp only [paddingInput]
    exact storeHalf_padding data hint
  | storeWord =>
    dsimp only [paddingInput]
    exact storeWord_padding data hint
  | storeDouble =>
    dsimp only [paddingInput]
    exact storeDouble_padding data hint
  | mul => exact MulChip.proverAssumptions_padding data hint
  | divRem => exact DivRemChip.proverAssumptions_padding data hint
  | aluX0 => exact AluX0Chip.proverAssumptions_padding data hint

/-- The per-chip physical input sequence, in scheduler order. -/
def inputs (id : InstructionChipId) (events : List id.Event) : List ((installed id).Input Fp) :=
  events.map (activeInput id) ++ List.replicate (demandPadding events.length) (paddingInput id)

@[simp] theorem inputs_length (id : InstructionChipId) (events : List id.Event) :
    (inputs id events).length = demandHeight events.length := by
  simp only [inputs, List.length_append, List.length_map, List.length_replicate, add_demandPadding]

private theorem inputs_valid (id : InstructionChipId) (events : List id.Event)
    (valid : ∀ e ∈ events, id.Valid e) (data : ProverData Fp) (hint : ProverHint Fp) :
    ∀ x ∈ inputs id events, (installed id).circuit.ProverAssumptions x data hint := by
  intro x member
  rcases List.mem_append.mp member with active | pad
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp active
    exact activeInput_valid id e (valid e he) data hint
  · rw [List.eq_of_mem_replicate pad]
    exact paddingInput_valid id data hint

/-- Build the physical rows of the installed component with Clean's canonical row generator. -/
def table (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size) : Table Fp :=
  Table.build (installed id) (inputs id events) ((installed id).inputData (inputs id events) data)
    hint (by rwa [inputs_length]) (by
      obtain ⟨mode, hmode, _⟩ := generation_padding id
      simp [Component.FixedRowsMatch, hmode]) ((installed id).inputData_consistent _ data)

/-- The exact installed rows satisfy all assertions, fixed lookups and channel guarantees. -/
theorem table_valid (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size)
    (valid : ∀ e ∈ events, id.Valid e) :
    (table id events data hint bounded).Constraints ∧ (table id events data hint bounded).Guarantees :=
  ⟨Table.build_constraints _ _ _ _ _ _ _ (inputs_valid id events valid _ hint),
   Table.build_guarantees _ _ _ _ _ _ _ (inputs_valid id events valid _ hint)⟩

/-- Every physical row remains checked when the complete inventory supplies its canonical data. -/
theorem constraints_at (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size)
    (valid : ∀ e ∈ events, id.Valid e) (evaluation : ProverData Fp) :
    ∀ row ∈ (table id events data hint bounded).table,
      (installed id).operations.ConstraintsHold (Environment.fromArray row evaluation) := by
  intro row member
  apply (installed id).constraintsHold_setData (data := (table id events data hint bounded).data)
  · rw [ProtectedOrdinaryReceipt.lookups, ProtectedOrdinaryReceipt.provider_lookups,
      supportedChipFor_lookups_empty]
  · exact (table_valid id events data hint bounded valid).1 row member

@[simp] theorem table_length (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size) :
    (table id events data hint bounded).length = demandHeight events.length := by
  simp only [table, Table.build_length, inputs_length]

/-- The entire receipt ledger is decoded from the registered physical rows in sequence. -/
theorem table_receipts (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size) :
    let built := table id events data hint bounded
    built.interactionsWith InstructionReceipt.channel.toRaw =
      built.table.map (fun physical =>
        let row := (supportedChipFor (p := SP1Prime) id).decodeRow built.data physical
        InstructionReceipt.channel.pushedIfValue row.is_real (statePushMessage row)) := by
  dsimp only
  simp only [Table.interactionsWith, Table.environment, table, Table.build_component, Table.build_data,
    ProtectedOrdinaryReceipt.row_receipt, List.map_eq_flatMap]

/-- A disabled receipt still costs one physical occurrence. -/
theorem table_receipt_count (id : InstructionChipId) (events : List id.Event) (data : ProverData Fp)
    (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size) :
    ((table id events data hint bounded).interactionsWith InstructionReceipt.channel.toRaw).length =
      demandHeight events.length := by
  rw [table_receipts, List.length_map]
  exact table_length id events data hint bounded

private theorem padding_gate (id : InstructionChipId)
    (cols : (supportedChipFor (p := SP1Prime) id).kind.Cols Fp) :
    ((supportedChipFor (p := SP1Prime) id).kind.view (paddingInput id) cols).is_real = 0 := by
  cases id <;> dsimp only [paddingInput]
  all_goals try rfl
  case loadByte =>
    change LoadByteChip.isReal (0 : LoadByteChip.Inputs Fp) = 0
    decide +kernel
  case loadHalf =>
    change LoadHalfChip.isReal (0 : LoadHalfChip.Inputs Fp) = 0
    decide +kernel
  case loadWord =>
    change LoadWordChip.isReal (0 : LoadWordChip.Inputs Fp) = 0
    decide +kernel
  case loadDouble =>
    change (0 : LoadDoubleChip.Inputs Fp).is_real = 0
    decide +kernel
  case loadX0 =>
    change LoadX0Chip.isReal (0 : LoadX0Chip.Inputs Fp) = 0
    decide +kernel
  case storeByte =>
    change (0 : StoreByteChip.Inputs Fp).is_real = 0
    decide +kernel
  case storeHalf =>
    change (0 : StoreHalfChip.Inputs Fp).is_real = 0
    decide +kernel
  case storeWord =>
    change (0 : StoreWordChip.Inputs Fp).is_real = 0
    decide +kernel
  case storeDouble =>
    change (0 : StoreDoubleChip.Inputs Fp).is_real = 0
    decide +kernel

/-- The decoded activity of a physical padding row is zero, even at different evaluation data. -/
theorem padding_inactive (id : InstructionChipId) (data evaluation : ProverData Fp)
    (hint : ProverHint Fp) :
    ((supportedChipFor (p := SP1Prime) id).decodeRow evaluation
      ((installed id).buildRow (paddingInput id) data hint)).is_real = 0 := by
  let chip := supportedChipFor (p := SP1Prime) id
  let env := Environment.fromArray ((installed id).buildRow (paddingInput id) data hint) evaluation
  change (chip.kind.view ((installed id).rowInput env) (chip.table.rowOutput env)).is_real = 0
  rw [(installed id).rowInput_buildRow (paddingInput id) data evaluation hint]
  exact padding_gate id _

private theorem active_gate (id : InstructionChipId) (event : id.Event) (valid : id.Valid event)
    (cols : (supportedChipFor (p := SP1Prime) id).kind.Cols Fp) :
    ((supportedChipFor (p := SP1Prime) id).kind.view (activeInput id event) cols).is_real = 1 := by
  cases id <;> try rfl
  case bitwise => exact (bitwiseFlags_spec (p := SP1Prime) valid.2).2.2.2
  case lt => exact (ltFlags_spec (p := SP1Prime) valid.2).2.2
  case shiftLeft => exact (shiftLeftFlags_spec (p := SP1Prime) valid.2).2.2
  case shiftRight => exact (shiftRightFlags_spec (p := SP1Prime) valid.2).2.2.2.2
  case branch => exact ITypeEvent.toBranchInputs_is_real valid.2.1
  case mul => exact (mulFlags_spec (p := SP1Prime) valid.2).2.2.2.2.2
  case loadByte =>
    change LoadByteChip.isReal (MemoryEvent.toLoadByteInputs event) = (1 : Fp)
    by_cases h : event.opcode = 29 <;> simp [LoadByteChip.isReal, MemoryEvent.toLoadByteInputs, h]
  case loadHalf =>
    change LoadHalfChip.isReal (MemoryEvent.toLoadHalfInputs event) = (1 : Fp)
    by_cases h : event.opcode = 30 <;> simp [LoadHalfChip.isReal, MemoryEvent.toLoadHalfInputs, h]
  case loadWord =>
    change LoadWordChip.isReal (MemoryEvent.toLoadWordInputs event) = (1 : Fp)
    by_cases h : event.opcode = 31 <;> simp [LoadWordChip.isReal, MemoryEvent.toLoadWordInputs, h]
  case loadX0 =>
    change LoadX0Chip.isReal (MemoryEvent.toLoadX0Inputs event) = (1 : Fp)
    rcases valid.2 with (h | h) | ⟨(h | h), _⟩ | ⟨(h | h), _⟩ | ⟨h, _⟩ <;>
      simp [LoadX0Chip.isReal, MemoryEvent.toLoadX0Inputs, h]

/-- The decoded activity of each correctly routed event survives generation and data replacement. -/
theorem active_is_real (id : InstructionChipId) (event : id.Event) (valid : id.Valid event)
    (data evaluation : ProverData Fp) (hint : ProverHint Fp) :
    ((supportedChipFor (p := SP1Prime) id).decodeRow evaluation
      ((installed id).buildRow (activeInput id event) data hint)).is_real = 1 := by
  let chip := supportedChipFor (p := SP1Prime) id
  let env := Environment.fromArray ((installed id).buildRow (activeInput id event) data hint) evaluation
  change (chip.kind.view ((installed id).rowInput env) (chip.table.rowOutput env)).is_real = 1
  rw [(installed id).rowInput_buildRow (activeInput id event) data evaluation hint]
  exact active_gate id event valid _

/-- The installed receipt ledger has an ordered unit-weight prefix and a zero-weight suffix. -/
theorem receipt_weights (id : InstructionChipId) (events : List id.Event)
    (data : ProverData Fp) (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size)
    (valid : ∀ e ∈ events, id.Valid e) :
    ((table id events data hint bounded).interactionsWith InstructionReceipt.channel.toRaw).map (·.mult) =
      List.replicate events.length 1 ++ List.replicate (demandPadding events.length) 0 := by
  rw [table_receipts]
  simp only [table, Table.build_table, Table.build_data, inputs, List.map_append, List.map_replicate,
    List.map_map, Function.comp_def, Channel.pushedIfValue, padding_inactive]
  congr 1
  calc _ = events.map (fun _ => (1 : Fp)) :=
          List.map_congr_left (fun e he => active_is_real id e (valid e he) _ _ hint)
       _ = _ := by simp

/-- Dropping the active input prefix leaves every zero-multiplicity receipt, in its physical slot. -/
theorem padding_receipt_weights (id : InstructionChipId) (events : List id.Event)
    (data : ProverData Fp) (hint : ProverHint Fp) (bounded : demandHeight events.length ≤ UInt64.size) :
    ((((table id events data hint bounded).interactionsWith InstructionReceipt.channel.toRaw).drop
      events.length).map (·.mult)) = List.replicate (demandPadding events.length) 0 := by
  rw [table_receipts]
  simp [table, inputs, Channel.pushedIfValue, padding_inactive]

end SP1Clean.TraceGen.InstalledInstructionTables
