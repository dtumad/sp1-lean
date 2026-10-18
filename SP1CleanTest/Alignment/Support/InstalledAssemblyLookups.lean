import ToClean.Gadgets.LookupProjection
import SP1CleanTest.Alignment.Support.InstalledAssembly
import ToClean.Air.EnsembleCheck

/-! # Lookup-free complete installed assembly -/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- All installed providers use AIR constraints and channels; no legacy lookup oracle remains. -/
def fixed (_context : Context) : List (FiniteLookup Fp) := []

/-- Component selection ranges over all 94 installed physical slots. -/
abbrev componentAt (context : Context) (index : Fin 94) : Component Fp :=
  (assembly context).tables[index.val]'(by change index.val < 94; exact index.isLt)

attribute [local circuit_norm]
  Gadgets.BitwiseByte.circuit
  Gadgets.Conditional.circuit
  Gadgets.Conditional.main
  Gadgets.Equality.circuit
  Gadgets.Equality.main
  Gadgets.IsEqual.circuit
  Gadgets.IsEqual.main
  Gadgets.IsZero.circuit
  Gadgets.IsZero.main
  Gadgets.IsZeroField.circuit
  SP1Clean.AddChip.circuit
  SP1Clean.AddChip.main
  SP1Clean.AddOperation.circuit
  SP1Clean.AddOperation.main
  SP1Clean.AddiChip.circuit
  SP1Clean.AddiChip.main
  SP1Clean.AddrAddOperation.circuit
  SP1Clean.AddrAddOperation.main
  SP1Clean.AddressDiv8.circuit
  SP1Clean.AddressDiv8.main
  SP1Clean.AddressOperation.circuit
  SP1Clean.AddressOperation.main
  SP1Clean.AddressOrder.circuit
  SP1Clean.AddressOrder.main
  SP1Clean.AddwChip.circuit
  SP1Clean.AddwChip.main
  SP1Clean.AddwOperation.circuit
  SP1Clean.AddwOperation.main
  SP1Clean.AluX0Chip.circuit
  SP1Clean.AluX0Chip.main
  SP1Clean.BitwiseChip.circuit
  SP1Clean.BitwiseChip.main
  SP1Clean.BitwiseOperation.circuit
  SP1Clean.BitwiseOperation.main
  SP1Clean.BitwiseU16Operation.circuit
  SP1Clean.BitwiseU16Operation.main
  SP1Clean.BoundedWord.circuit
  SP1Clean.BoundedWord.main
  SP1Clean.BranchChip.circuit
  SP1Clean.BranchChip.main
  SP1Clean.ByteChip.AndByte.circuit
  SP1Clean.ByteChip.AndByte.main
  SP1Clean.ByteChip.Ltu.circuit
  SP1Clean.ByteChip.Ltu.main
  SP1Clean.ByteChip.MSB.circuit
  SP1Clean.ByteChip.MSB.main
  SP1Clean.ByteChip.OrByte.circuit
  SP1Clean.ByteChip.OrByte.main
  SP1Clean.ByteChip.U8Range.circuit
  SP1Clean.ByteChip.U8Range.main
  SP1Clean.ByteChip.XorByte.circuit
  SP1Clean.ByteChip.XorByte.main
  SP1Clean.ClockOrder.circuit
  SP1Clean.ClockOrder.main
  SP1Clean.CoreSyscallChip.circuit
  SP1Clean.CoreSyscallChip.main
  SP1Clean.DivRemChip.circuit
  SP1Clean.DivRemChip.main
  SP1Clean.DivRemCompare.circuit
  SP1Clean.DivRemCompare.main
  SP1Clean.DivRemCore.circuit
  SP1Clean.DivRemCore.main
  SP1Clean.FinalMemoryChange.circuit
  SP1Clean.FinalMemoryChange.main
  SP1Clean.FinalMemoryChangeBoundary.circuit
  SP1Clean.FinalMemoryChangeBoundary.main
  SP1Clean.FinalMemoryReceipt.circuit
  SP1Clean.FinalRamCheck.circuit
  SP1Clean.FinalRamCheck.main
  SP1Clean.FinalRamProvider.circuit
  SP1Clean.FinalRamProvider.main
  SP1Clean.FinalRamValue.circuit
  SP1Clean.FinalRamValue.main
  SP1Clean.FinalRegisterCheck.circuit
  SP1Clean.FinalRegisterCheck.main
  SP1Clean.FinalRegisterProvider.circuit
  SP1Clean.FinalRegisterProvider.main
  SP1Clean.FinalRegisterValue.circuit
  SP1Clean.FinalRegisterValue.main
  SP1Clean.HaltChip.circuit
  SP1Clean.HaltChip.main
  SP1Clean.HaltPaddingChip.circuit
  SP1Clean.HaltPaddingChip.main
  SP1Clean.HintReadSpan.circuit
  SP1Clean.HintReadSpan.main
  SP1Clean.HintReadStep.circuit
  SP1Clean.HintReadStep.main
  SP1Clean.HintReadWordChip.circuit
  SP1Clean.HintReadWordChip.main
  SP1Clean.HostBoundary.circuit
  SP1Clean.HostBoundary.main
  SP1Clean.HostCallChip.circuit
  SP1Clean.HostCallChip.main
  SP1Clean.HostCommitChip.circuit
  SP1Clean.HostCommitChip.main
  SP1Clean.HostCommitEndpoint.circuit
  SP1Clean.HostCommitEndpoint.main
  SP1Clean.HostEnterChip.circuit
  SP1Clean.HostEnterChip.main
  SP1Clean.HostExitBoundary.circuit
  SP1Clean.HostExitBoundary.main
  SP1Clean.HostHaltChip.circuit
  SP1Clean.HostHaltChip.main
  SP1Clean.HostHintLengthChip.circuit
  SP1Clean.HostHintLengthChip.main
  SP1Clean.HostHintQueueBoundary.circuit
  SP1Clean.HostHintQueueBoundary.main
  SP1Clean.HostHintReadChip.circuit
  SP1Clean.HostHintReadChip.main
  SP1Clean.HostRamAccessChip.circuit
  SP1Clean.HostRamAccessChip.main
  SP1Clean.InitialMemoryLookup.circuit
  SP1Clean.InitialMemoryLookup.main
  SP1Clean.InitialMemoryRead.circuit
  SP1Clean.InitialMemoryRead.main
  SP1Clean.InitialRamProvider.circuit
  SP1Clean.InitialRamProvider.main
  SP1Clean.InitialRegisterProvider.circuit
  SP1Clean.InitialRegisterProvider.main
  SP1Clean.IsEqualWordOperation.circuit
  SP1Clean.IsEqualWordOperation.main
  SP1Clean.IsZeroOperation.circuit
  SP1Clean.IsZeroOperation.main
  SP1Clean.IsZeroWordOperation.circuit
  SP1Clean.IsZeroWordOperation.main
  SP1Clean.JalChip.circuit
  SP1Clean.JalChip.main
  SP1Clean.JalrChip.circuit
  SP1Clean.JalrChip.main
  SP1Clean.LoadByteChip.circuit
  SP1Clean.LoadByteChip.main
  SP1Clean.LoadDoubleChip.circuit
  SP1Clean.LoadDoubleChip.main
  SP1Clean.LoadHalfChip.circuit
  SP1Clean.LoadHalfChip.main
  SP1Clean.LoadWordChip.circuit
  SP1Clean.LoadWordChip.main
  SP1Clean.LoadX0Chip.circuit
  SP1Clean.LoadX0Chip.main
  SP1Clean.LtChip.circuit
  SP1Clean.LtChip.main
  SP1Clean.LtOperationSigned.circuit
  SP1Clean.LtOperationSigned.main
  SP1Clean.LtOperationUnsigned.circuit
  SP1Clean.LtOperationUnsigned.main
  SP1Clean.MemoryBumpChip.circuit
  SP1Clean.MemoryBumpChip.main
  SP1Clean.MemoryFinalizeChip.circuit
  SP1Clean.MemoryFinalizeChip.main
  SP1Clean.MemoryProviderChip.circuit
  SP1Clean.MemoryProviderChip.main
  SP1Clean.MulChip.circuit
  SP1Clean.MulChip.main
  SP1Clean.MulOperation.circuit
  SP1Clean.MulOperation.main
  SP1Clean.OrderedBoundary.circuit
  SP1Clean.OrderedBoundary.main
  SP1Clean.OrderedBoundaryEnd.circuit
  SP1Clean.OrderedBoundaryEnd.main
  SP1Clean.OrderedBoundaryVerifier.circuit
  SP1Clean.OrderedBoundaryVerifier.main
  SP1Clean.OrderedInitialProvider.circuit
  SP1Clean.OrderedInitialProvider.main
  SP1Clean.OrderedMemoryProvider.circuit
  SP1Clean.OrderedMemoryProvider.main
  SP1Clean.OrderedSnapshotProvider.circuit
  SP1Clean.ProgramProviderChip.circuit
  SP1Clean.ProgramProviderChip.main
  SP1Clean.RangeChip.circuit
  SP1Clean.RangeChip.main
  SP1Clean.Readers.ALUTypeReader.circuit
  SP1Clean.Readers.ALUTypeReader.main
  SP1Clean.Readers.ALUTypeReaderImmutable.circuit
  SP1Clean.Readers.ALUTypeReaderImmutable.main
  SP1Clean.Readers.CPUState.circuit
  SP1Clean.Readers.CPUState.main
  SP1Clean.Readers.ITypeReader.circuit
  SP1Clean.Readers.ITypeReader.main
  SP1Clean.Readers.ITypeReaderImmutable.circuit
  SP1Clean.Readers.ITypeReaderImmutable.main
  SP1Clean.Readers.JTypeReader.circuit
  SP1Clean.Readers.JTypeReader.main
  SP1Clean.Readers.MemoryAccess.circuit
  SP1Clean.Readers.MemoryAccess.main
  SP1Clean.Readers.RTypeReader.circuit
  SP1Clean.Readers.RTypeReader.main
  SP1Clean.Readers.RegisterAccessCols.circuit
  SP1Clean.Readers.RegisterAccessCols.main
  SP1Clean.Readers.RegisterAccessTimestamp.circuit
  SP1Clean.Readers.RegisterAccessTimestamp.main
  SP1Clean.Readers.RegisterRead.circuit
  SP1Clean.Readers.RegisterRead.main
  SP1Clean.Readers.RegisterWrite.circuit
  SP1Clean.Readers.RegisterWrite.main
  SP1Clean.ShiftLeftChip.circuit
  SP1Clean.ShiftLeftChip.main
  SP1Clean.ShiftLeftCore.circuit
  SP1Clean.ShiftLeftCore.main
  SP1Clean.ShiftRightChip.circuit
  SP1Clean.ShiftRightChip.main
  SP1Clean.ShiftRightCore.circuit
  SP1Clean.ShiftRightCore.main
  SP1Clean.SnapshotRamProvider.circuit
  SP1Clean.SnapshotRamProvider.main
  SP1Clean.SnapshotRegisterProvider.circuit
  SP1Clean.SnapshotRegisterProvider.main
  SP1Clean.Soundness.SupportedChip.circuit
  SP1Clean.StateBumpChip.circuit
  SP1Clean.StateBumpChip.main
  SP1Clean.StoreByteChip.circuit
  SP1Clean.StoreByteChip.main
  SP1Clean.StoreDoubleChip.circuit
  SP1Clean.StoreDoubleChip.main
  SP1Clean.StoreHalfChip.circuit
  SP1Clean.StoreHalfChip.main
  SP1Clean.StoreWordChip.circuit
  SP1Clean.StoreWordChip.main
  SP1Clean.SubChip.circuit
  SP1Clean.SubChip.main
  SP1Clean.SubOperation.circuit
  SP1Clean.SubOperation.main
  SP1Clean.SubwChip.circuit
  SP1Clean.SubwChip.main
  SP1Clean.SubwOperation.circuit
  SP1Clean.SubwOperation.main
  SP1Clean.SyscallCodeGuard.circuit
  SP1Clean.SyscallCodeGuard.main
  SP1Clean.SyscallInstrsChip.CommitArm.circuit
  SP1Clean.SyscallInstrsChip.CommitArm.main
  SP1Clean.SyscallInstrsChip.DispatchArm.circuit
  SP1Clean.SyscallInstrsChip.DispatchArm.main
  SP1Clean.SyscallInstrsChip.FieldBoundArm.circuit
  SP1Clean.SyscallInstrsChip.FieldBoundArm.main
  SP1Clean.SyscallInstrsChip.PcArm.circuit
  SP1Clean.SyscallInstrsChip.PcArm.main
  SP1Clean.SyscallInstrsChip.WriteArm.circuit
  SP1Clean.SyscallInstrsChip.WriteArm.main
  SP1Clean.SyscallInstrsChip.circuit
  SP1Clean.SyscallInstrsChip.main
  SP1Clean.U16CompareOperation.circuit
  SP1Clean.U16CompareOperation.main
  SP1Clean.U16MSBOperation.circuit
  SP1Clean.U16MSBOperation.main
  SP1Clean.U16toU8OperationSafe.circuit
  SP1Clean.U16toU8OperationSafe.main
  SP1Clean.UTypeChip.circuit
  SP1Clean.UTypeChip.main
  SP1Clean.WordRangeCheck.circuit
  SP1Clean.WordRangeCheck.main
  SP1Clean.WritePermissionProvider.circuit
  SP1Clean.WritePermissionProvider.main


attribute [local circuit_norm] supportedChipFor RangeChip.circuitFor
  ProtectedStore.byte ProtectedStore.half ProtectedStore.word ProtectedStore.double
  DivRemChip.populateRow DivRemChip.constrainRow DivRemChip.assertZeros
  HostHintQueue.source HostHintQueue.sourceWord
  StaticTable.payloadComponent StaticTable.payloadProvider
  HostCommitBoundary.terminal HostCommitBoundary.terminalMain

-- Normalize proof-bearing wrappers only through their operation projection lemmas.
attribute [local circuit_norm] List.append_eq Component.rowOperations
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  GeneralFormalCircuit.WithHint.toSubcircuit_lookups FormalCircuit.toSubcircuit_lookups
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups
  Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits
  InitialMemoryLookup.circuitNamed InitialMemoryRead.circuitNamed
  OrderedFinalProvider.registerCircuit OrderedFinalProvider.ramCircuit

/-- No legacy lookup at physical component 0. -/
private theorem lookup_slot_0 (context : Context) :
    (componentAt context 0).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 1. -/
private theorem lookup_slot_1 (context : Context) :
    (componentAt context 1).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 2. -/
private theorem lookup_slot_2 (context : Context) :
    (componentAt context 2).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 3. -/
private theorem lookup_slot_3 (context : Context) :
    (componentAt context 3).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 4. -/
private theorem lookup_slot_4 (context : Context) :
    (componentAt context 4).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 5. -/
private theorem lookup_slot_5 (context : Context) :
    (componentAt context 5).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 6. -/
private theorem lookup_slot_6 (context : Context) :
    (componentAt context 6).rowOperations.lookups.map (·.table) = [] := by
  change (FixedProgramProvider.Preprocessed.component (p := SP1Prime) context.image).rowOperations.lookups.map (·.table) = []
  rw [← Component.lookups_eq, FixedProgramProvider.Preprocessed.component_lookups]
  rfl

/-- No legacy lookup at physical component 7. -/
private theorem lookup_slot_7 (context : Context) :
    (componentAt context 7).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 8. -/
private theorem lookup_slot_8 (context : Context) :
    (componentAt context 8).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 9. -/
private theorem lookup_slot_9 (context : Context) :
    (componentAt context 9).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 10. -/
private theorem lookup_slot_10 (context : Context) :
    (componentAt context 10).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 11. -/
private theorem lookup_slot_11 (context : Context) :
    (componentAt context 11).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 12. -/
private theorem lookup_slot_12 (context : Context) :
    (componentAt context 12).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 13. -/
private theorem lookup_slot_13 (context : Context) :
    (componentAt context 13).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 14. -/
private theorem lookup_slot_14 (context : Context) :
    (componentAt context 14).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 15. -/
private theorem lookup_slot_15 (context : Context) :
    (componentAt context 15).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 16. -/
private theorem lookup_slot_16 (context : Context) :
    (componentAt context 16).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 17. -/
private theorem lookup_slot_17 (context : Context) :
    (componentAt context 17).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 18. -/
private theorem lookup_slot_18 (context : Context) :
    (componentAt context 18).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 19. -/
private theorem lookup_slot_19 (context : Context) :
    (componentAt context 19).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 20. -/
private theorem lookup_slot_20 (context : Context) :
    (componentAt context 20).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 21. -/
private theorem lookup_slot_21 (context : Context) :
    (componentAt context 21).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 22. -/
private theorem lookup_slot_22 (context : Context) :
    (componentAt context 22).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 23. -/
private theorem lookup_slot_23 (context : Context) :
    (componentAt context 23).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 24. -/
private theorem lookup_slot_24 (context : Context) :
    (componentAt context 24).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 25. -/
private theorem lookup_slot_25 (context : Context) :
    (componentAt context 25).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 26. -/
private theorem lookup_slot_26 (context : Context) :
    (componentAt context 26).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 27. -/
private theorem lookup_slot_27 (context : Context) :
    (componentAt context 27).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 28. -/
private theorem lookup_slot_28 (context : Context) :
    (componentAt context 28).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 29. -/
private theorem lookup_slot_29 (context : Context) :
    (componentAt context 29).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 30. -/
private theorem lookup_slot_30 (context : Context) :
    (componentAt context 30).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 31. -/
private theorem lookup_slot_31 (context : Context) :
    (componentAt context 31).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 32. -/
private theorem lookup_slot_32 (context : Context) :
    (componentAt context 32).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 33. -/
private theorem lookup_slot_33 (context : Context) :
    (componentAt context 33).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 34. -/
private theorem lookup_slot_34 (context : Context) :
    (componentAt context 34).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 35. -/
private theorem lookup_slot_35 (context : Context) :
    (componentAt context 35).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 36. -/
private theorem lookup_slot_36 (context : Context) :
    (componentAt context 36).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 37. -/
private theorem lookup_slot_37 (context : Context) :
    (componentAt context 37).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 38. -/
private theorem lookup_slot_38 (context : Context) :
    (componentAt context 38).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 39. -/
private theorem lookup_slot_39 (context : Context) :
    (componentAt context 39).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 40. -/
private theorem lookup_slot_40 (context : Context) :
    (componentAt context 40).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 41. -/
private theorem lookup_slot_41 (context : Context) :
    (componentAt context 41).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 42. -/
private theorem lookup_slot_42 (context : Context) :
    (componentAt context 42).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 43. -/
private theorem lookup_slot_43 (context : Context) :
    (componentAt context 43).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 44. -/
private theorem lookup_slot_44 (context : Context) :
    (componentAt context 44).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 45. -/
private theorem lookup_slot_45 (context : Context) :
    (componentAt context 45).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 46. -/
private theorem lookup_slot_46 (context : Context) :
    (componentAt context 46).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 47. -/
private theorem lookup_slot_47 (context : Context) :
    (componentAt context 47).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 48. -/
private theorem lookup_slot_48 (context : Context) :
    (componentAt context 48).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 49. -/
private theorem lookup_slot_49 (context : Context) :
    (componentAt context 49).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 50. -/
private theorem lookup_slot_50 (context : Context) :
    (componentAt context 50).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 51. -/
private theorem lookup_slot_51 (context : Context) :
    (componentAt context 51).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 52. -/
private theorem lookup_slot_52 (context : Context) :
    (componentAt context 52).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 53. -/
private theorem lookup_slot_53 (context : Context) :
    (componentAt context 53).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 54. -/
private theorem lookup_slot_54 (context : Context) :
    (componentAt context 54).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 55. -/
private theorem lookup_slot_55 (context : Context) :
    (componentAt context 55).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 56. -/
private theorem lookup_slot_56 (context : Context) :
    (componentAt context 56).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 57. -/
private theorem lookup_slot_57 (context : Context) :
    (componentAt context 57).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 58. -/
private theorem lookup_slot_58 (context : Context) :
    (componentAt context 58).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, Circuit.foldlRange.operations_eq, List.ofFn_succ]

/-- The verifier-fixed membership provider has no legacy lookups. -/
private theorem lookup_slot_59 (context : Context) :
    (componentAt context 59).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- No legacy lookup at physical component 61. -/
private theorem lookup_slot_61 (context : Context) :
    (componentAt context 61).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- The fixed writable-interval provider has no legacy lookup. -/
private theorem lookup_slot_62 (context : Context) :
    (componentAt context 62).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- No legacy lookup at physical component 63. -/
private theorem lookup_slot_63 (context : Context) :
    (componentAt context 63).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 64. -/
private theorem lookup_slot_64 (context : Context) :
    (componentAt context 64).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 65. -/
private theorem lookup_slot_65 (context : Context) :
    (componentAt context 65).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 66. -/
private theorem lookup_slot_66 (context : Context) :
    (componentAt context 66).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 67. -/
private theorem lookup_slot_67 (context : Context) :
    (componentAt context 67).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 68. -/
private theorem lookup_slot_68 (context : Context) :
    (componentAt context 68).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 69. -/
private theorem lookup_slot_69 (context : Context) :
    (componentAt context 69).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 70. -/
private theorem lookup_slot_70 (context : Context) :
    (componentAt context 70).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 71. -/
private theorem lookup_slot_71 (context : Context) :
    (componentAt context 71).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 72. -/
private theorem lookup_slot_72 (context : Context) :
    (componentAt context 72).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 73. -/
private theorem lookup_slot_73 (context : Context) :
    (componentAt context 73).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 74. -/
private theorem lookup_slot_74 (context : Context) :
    (componentAt context 74).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 75. -/
private theorem lookup_slot_75 (context : Context) :
    (componentAt context 75).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 76. -/
private theorem lookup_slot_76 (context : Context) :
    (componentAt context 76).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 77. -/
private theorem lookup_slot_77 (context : Context) :
    (componentAt context 77).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 78. -/
private theorem lookup_slot_78 (context : Context) :
    (componentAt context 78).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 79. -/
private theorem lookup_slot_79 (context : Context) :
    (componentAt context 79).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 80. -/
private theorem lookup_slot_80 (context : Context) :
    (componentAt context 80).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 81. -/
private theorem lookup_slot_81 (context : Context) :
    (componentAt context 81).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 82. -/
private theorem lookup_slot_82 (context : Context) :
    (componentAt context 82).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 83. -/
private theorem lookup_slot_83 (context : Context) :
    (componentAt context 83).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 84. -/
private theorem lookup_slot_84 (context : Context) :
    (componentAt context 84).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 85. -/
private theorem lookup_slot_85 (context : Context) :
    (componentAt context 85).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 86. -/
private theorem lookup_slot_86 (context : Context) :
    (componentAt context 86).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 87. -/
private theorem lookup_slot_87 (context : Context) :
    (componentAt context 87).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 88. -/
private theorem lookup_slot_88 (context : Context) :
    (componentAt context 88).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 89. -/
private theorem lookup_slot_89 (context : Context) :
    (componentAt context 89).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 90. -/
private theorem lookup_slot_90 (context : Context) :
    (componentAt context 90).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- No legacy lookup at physical component 91. -/
private theorem lookup_slot_91 (context : Context) :
    (componentAt context 91).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- The fixed target provider has no legacy lookup. -/
private theorem lookup_slot_92 (context : Context) :
    (componentAt context 92).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- The fixed RAM provider has no legacy lookup. -/
private theorem lookup_slot_60 (context : Context) :
    (componentAt context 60).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- The fixed RAM provider has no legacy lookup. -/
private theorem lookup_slot_93 (context : Context) :
    (componentAt context 93).rowOperations.lookups.map (·.table) = [] := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- Each installed component has exactly its listed fixed-table predicates. -/
theorem lookup_slot (context : Context) (index : Fin 94) :
    (componentAt context index).rowOperations.lookups.map (·.table) = [] := by
  fin_cases index
  · exact lookup_slot_0 context
  · exact lookup_slot_1 context
  · exact lookup_slot_2 context
  · exact lookup_slot_3 context
  · exact lookup_slot_4 context
  · exact lookup_slot_5 context
  · exact lookup_slot_6 context
  · exact lookup_slot_7 context
  · exact lookup_slot_8 context
  · exact lookup_slot_9 context
  · exact lookup_slot_10 context
  · exact lookup_slot_11 context
  · exact lookup_slot_12 context
  · exact lookup_slot_13 context
  · exact lookup_slot_14 context
  · exact lookup_slot_15 context
  · exact lookup_slot_16 context
  · exact lookup_slot_17 context
  · exact lookup_slot_18 context
  · exact lookup_slot_19 context
  · exact lookup_slot_20 context
  · exact lookup_slot_21 context
  · exact lookup_slot_22 context
  · exact lookup_slot_23 context
  · exact lookup_slot_24 context
  · exact lookup_slot_25 context
  · exact lookup_slot_26 context
  · exact lookup_slot_27 context
  · exact lookup_slot_28 context
  · exact lookup_slot_29 context
  · exact lookup_slot_30 context
  · exact lookup_slot_31 context
  · exact lookup_slot_32 context
  · exact lookup_slot_33 context
  · exact lookup_slot_34 context
  · exact lookup_slot_35 context
  · exact lookup_slot_36 context
  · exact lookup_slot_37 context
  · exact lookup_slot_38 context
  · exact lookup_slot_39 context
  · exact lookup_slot_40 context
  · exact lookup_slot_41 context
  · exact lookup_slot_42 context
  · exact lookup_slot_43 context
  · exact lookup_slot_44 context
  · exact lookup_slot_45 context
  · exact lookup_slot_46 context
  · exact lookup_slot_47 context
  · exact lookup_slot_48 context
  · exact lookup_slot_49 context
  · exact lookup_slot_50 context
  · exact lookup_slot_51 context
  · exact lookup_slot_52 context
  · exact lookup_slot_53 context
  · exact lookup_slot_54 context
  · exact lookup_slot_55 context
  · exact lookup_slot_56 context
  · exact lookup_slot_57 context
  · exact lookup_slot_58 context
  · exact lookup_slot_59 context
  · exact lookup_slot_60 context
  · exact lookup_slot_61 context
  · exact lookup_slot_62 context
  · exact lookup_slot_63 context
  · exact lookup_slot_64 context
  · exact lookup_slot_65 context
  · exact lookup_slot_66 context
  · exact lookup_slot_67 context
  · exact lookup_slot_68 context
  · exact lookup_slot_69 context
  · exact lookup_slot_70 context
  · exact lookup_slot_71 context
  · exact lookup_slot_72 context
  · exact lookup_slot_73 context
  · exact lookup_slot_74 context
  · exact lookup_slot_75 context
  · exact lookup_slot_76 context
  · exact lookup_slot_77 context
  · exact lookup_slot_78 context
  · exact lookup_slot_79 context
  · exact lookup_slot_80 context
  · exact lookup_slot_81 context
  · exact lookup_slot_82 context
  · exact lookup_slot_83 context
  · exact lookup_slot_84 context
  · exact lookup_slot_85 context
  · exact lookup_slot_86 context
  · exact lookup_slot_87 context
  · exact lookup_slot_88 context
  · exact lookup_slot_89 context
  · exact lookup_slot_90 context
  · exact lookup_slot_91 context
  · exact lookup_slot_92 context
  · exact lookup_slot_93 context

/-- Every installed component is lookup-free, including currently unused physical slots. -/
theorem component_lookups (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) : component.operations.lookups = [] := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  rw [Component.lookups_eq]
  exact List.map_eq_nil_iff.mp (lookup_slot context ⟨index, bound⟩)

/-- The empty lookup inventory covers every installed operation. -/
theorem lookups_complete (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) (lookup : Lookup Fp)
    (used : lookup ∈ component.operations.lookups) :
    ∃ fixedTable ∈ fixed context, fixedTable.table = lookup.table := by
  rw [component_lookups context component member] at used
  exact False.elim (List.not_mem_nil used)


end SP1CleanTest.Alignment.InstalledAssembly
