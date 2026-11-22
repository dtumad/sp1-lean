import SP1Clean.Export.InstalledFixedInventory

/-! # Per-channel widths of the 25 installed ordinary instruction circuits

The kernel checks every physical row, including guard-disabled emissions, protected-store
permission requests and the final ordinary receipt. Each check reduces the native circuit's
own interaction list after composing its proved subcircuits.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Soundness

/-- Maximum number of occurrences on a named channel in one physical ordinary instruction row. -/
def ordinaryRowBound (name : String) : Nat :=
  if name = (Channels.byteChannel (p := SP1Prime)).name then 126
  else if name = (Channels.memoryChannel (p := SP1Prime)).name then 6
  else if name = (WritePermissionProvider.channel (p := SP1Prime)).name then 8
  else if name = (Channels.stateChannel (p := SP1Prime)).name then 2
  else if name = (Channels.programChannel (p := SP1Prime)).name then 1
  else if name = (InstructionReceipt.channel (p := SP1Prime)).name then 1
  else 0
private def widthsCheck (names : List String) : Bool :=
  names.eraseDups.all fun name => decide (names.count name ≤ ordinaryRowBound name)
private def withReceipt (names : List String) : Bool :=
  widthsCheck (names ++ [(InstructionReceipt.channel (p := SP1Prime)).name])

private theorem raw_receipt {I O : TypeMap} [ProvableType I] [ProvableType O]
    (provider : GeneralFormalCircuit Fp I O) (project : Receipt.Projection Fp I Channels.StateMsg)
    (input : Var I Fp) (offset : ℕ) :
    (((InstructionReceipt.circuit provider project).main input).operations offset).interactions.map (·.channel.name) =
    ((provider.main input).operations offset).interactions.map (·.channel.name) ++
      [(InstructionReceipt.channel (p := SP1Prime)).name] := by
  simp only [InstructionReceipt.circuit, Receipt.circuit, Receipt.main,
    GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm, List.map_append, List.map_cons, List.map_nil]

section
attribute [local circuit_norm] AddChip.main AddOperation.circuit AddOperation.main AddiChip.main
attribute [local circuit_norm] AddrAddOperation.circuit AddrAddOperation.main AddressOperation.circuit AddressOperation.main
attribute [local circuit_norm] AddwChip.main AddwOperation.circuit AddwOperation.main AluX0Chip.main
attribute [local circuit_norm] BitwiseChip.main BitwiseOperation.circuit BitwiseOperation.main BitwiseU16Operation.circuit
attribute [local circuit_norm] BitwiseU16Operation.main BranchChip.main DivRemChip.assertZeros DivRemChip.constrainRow
attribute [local circuit_norm] DivRemChip.main DivRemChip.populateRow DivRemCompare.circuit DivRemCompare.main
attribute [local circuit_norm] DivRemCore.circuit DivRemCore.main Gadgets.Equality.circuit Gadgets.Equality.main
attribute [local circuit_norm] IsEqualWordOperation.circuit IsEqualWordOperation.main IsZeroOperation.circuit IsZeroOperation.main
attribute [local circuit_norm] IsZeroWordOperation.circuit IsZeroWordOperation.main JalChip.main JalrChip.main
attribute [local circuit_norm] LoadByteChip.main LoadDoubleChip.main LoadHalfChip.main LoadWordChip.main
attribute [local circuit_norm] LoadX0Chip.main LtChip.main LtOperationSigned.circuit LtOperationSigned.main
attribute [local circuit_norm] LtOperationUnsigned.circuit LtOperationUnsigned.main MulChip.main MulOperation.circuit
attribute [local circuit_norm] MulOperation.main ProtectedStore.byte ProtectedStore.double ProtectedStore.half
attribute [local circuit_norm] ProtectedStore.word Readers.ALUTypeReader.circuit Readers.ALUTypeReader.main Readers.ALUTypeReaderImmutable.circuit
attribute [local circuit_norm] Readers.ALUTypeReaderImmutable.main Readers.CPUState.circuit Readers.CPUState.main Readers.ITypeReader.circuit
attribute [local circuit_norm] Readers.ITypeReader.main Readers.ITypeReaderImmutable.circuit Readers.ITypeReaderImmutable.main Readers.JTypeReader.circuit
attribute [local circuit_norm] Readers.JTypeReader.main Readers.MemoryAccess.circuit Readers.MemoryAccess.main Readers.RTypeReader.circuit
attribute [local circuit_norm] Readers.RTypeReader.main Readers.RegisterAccessCols.circuit Readers.RegisterAccessCols.main Readers.RegisterAccessTimestamp.circuit
attribute [local circuit_norm] Readers.RegisterAccessTimestamp.main Readers.RegisterWrite.circuit Readers.RegisterWrite.main ShiftLeftChip.main
attribute [local circuit_norm] ShiftLeftCore.circuit ShiftLeftCore.main ShiftRightChip.main ShiftRightCore.circuit
attribute [local circuit_norm] ShiftRightCore.main StoreByteChip.circuit StoreByteChip.main StoreDoubleChip.circuit
attribute [local circuit_norm] StoreDoubleChip.main StoreHalfChip.circuit StoreHalfChip.main StoreWordChip.circuit
attribute [local circuit_norm] StoreWordChip.main SubChip.main SubOperation.circuit SubOperation.main
attribute [local circuit_norm] SubwChip.main SubwOperation.circuit SubwOperation.main U16CompareOperation.circuit
attribute [local circuit_norm] U16CompareOperation.main U16MSBOperation.circuit U16MSBOperation.main U16toU8OperationSafe.circuit
attribute [local circuit_norm] U16toU8OperationSafe.main UTypeChip.main
attribute [local circuit_norm] GeneralFormalCircuit.toSubcircuit_interactions
attribute [local circuit_norm] FormalCircuit.toSubcircuit_interactions FormalAssertion.toSubcircuit_interactions
attribute [local circuit_norm] List.map_append List.map_cons List.map_nil

local macro "check_ordinary_channels" : tactic => `(tactic| (simp only [circuit_norm]; first | rfl | decide +kernel))

private theorem add_channels (input : Var AddChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((AddChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem addi_channels (input : Var AddiChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((AddiChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem addw_channels (input : Var AddwChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((AddwChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem sub_channels (input : Var SubChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((SubChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem subw_channels (input : Var SubwChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((SubwChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem bitwise_channels (input : Var BitwiseChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((BitwiseChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem lt_channels (input : Var LtChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LtChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem shiftLeft_channels (input : Var ShiftLeftChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ShiftLeftChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem shiftRight_channels (input : Var ShiftRightChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ShiftRightChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem jal_channels (input : Var JalChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((JalChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem jalr_channels (input : Var JalrChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((JalrChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem branch_channels (input : Var BranchChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((BranchChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem uType_channels (input : Var UTypeChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((UTypeChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem loadByte_channels (input : Var LoadByteChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LoadByteChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem loadHalf_channels (input : Var LoadHalfChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LoadHalfChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem loadWord_channels (input : Var LoadWordChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LoadWordChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem loadDouble_channels (input : Var LoadDoubleChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LoadDoubleChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem loadX0_channels (input : Var LoadX0Chip.Inputs Fp) (offset : ℕ) :
    withReceipt (((LoadX0Chip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem storeByte_channels (input : Var StoreByteChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ProtectedStore.byte.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem storeHalf_channels (input : Var StoreHalfChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ProtectedStore.half.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem storeWord_channels (input : Var StoreWordChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ProtectedStore.word.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem storeDouble_channels (input : Var StoreDoubleChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((ProtectedStore.double.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem mul_channels (input : Var MulChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((MulChip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

private theorem divRem_channels (input : Var DivRemChip.Inputs Fp) (offset : ℕ) :
    withReceipt (((DivRemChip.main input).operations offset).interactions.map (·.channel.name)) := by
  simp only [circuit_norm]
  decide +kernel

private theorem aluX0_channels (input : Var AluX0Chip.Inputs Fp) (offset : ℕ) :
    withReceipt (((AluX0Chip.main input).operations offset).interactions.map (·.channel.name)) := by
  check_ordinary_channels

end

private theorem checked_row (id : InstructionChipId) :
    widthsCheck (rowChannelNames (ProtectedOrdinaryReceipt.component id)) := by
  rw [rowChannelNames, Component.interactions_eq, Component.rowOperations]
  change widthsCheck ((((InstructionReceipt.circuit _ _).main _).operations _).interactions.map _)
  refine (congrArg widthsCheck (@raw_receipt _ _ (supportedChipFor (p := SP1Prime) id).kind.provableInputs
    (supportedChipFor (p := SP1Prime) id).kind.provableCols (ProtectedOrdinaryReceipt.provider id)
    (OrdinaryStateReceipt.projection id) _ _)).trans ?_
  cases id with
  | add => exact add_channels _ _
  | addi => exact addi_channels _ _
  | addw => exact addw_channels _ _
  | sub => exact sub_channels _ _
  | subw => exact subw_channels _ _
  | bitwise => exact bitwise_channels _ _
  | lt => exact lt_channels _ _
  | shiftLeft => exact shiftLeft_channels _ _
  | shiftRight => exact shiftRight_channels _ _
  | jal => exact jal_channels _ _
  | jalr => exact jalr_channels _ _
  | branch => exact branch_channels _ _
  | uType => exact uType_channels _ _
  | loadByte => exact loadByte_channels _ _
  | loadHalf => exact loadHalf_channels _ _
  | loadWord => exact loadWord_channels _ _
  | loadDouble => exact loadDouble_channels _ _
  | loadX0 => exact loadX0_channels _ _
  | storeByte => exact storeByte_channels _ _
  | storeHalf => exact storeHalf_channels _ _
  | storeWord => exact storeWord_channels _ _
  | storeDouble => exact storeDouble_channels _ _
  | mul => exact mul_channels _ _
  | divRem => exact divRem_channels _ _
  | aluX0 => exact aluX0_channels _ _

/-- The count used by the installed verifier itself is bounded on every channel name.
Names outside the six physical protocols have zero width. -/
theorem ordinary_row_width (id : InstructionChipId) (name : String) :
    rowOccurrences (ProtectedOrdinaryReceipt.component id) name ≤ ordinaryRowBound name := by
  let table := ProtectedOrdinaryReceipt.component (p := SP1Prime) id
  have cost : rowOccurrences table name = (rowChannelNames table).count name := by
    simp [rowOccurrences, rowChannelNames, List.count_eq_countP, List.countP_map, Function.comp_def]
  rw [cost]
  by_cases present : name ∈ rowChannelNames table
  · exact of_decide_eq_true ((List.all_eq_true.mp (checked_row id)) name (by simpa using present))
  · simp [List.count_eq_zero.mpr present]

/-- The Byte ledger has the largest ordinary-row width across the registry. -/
theorem ordinaryRowBound_le (name : String) : ordinaryRowBound name ≤ 126 := by
  unfold ordinaryRowBound
  split <;> repeat' first | split | decide

end SP1Clean.Export.InstalledAssembly
