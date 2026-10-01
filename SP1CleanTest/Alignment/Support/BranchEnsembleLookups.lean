import ToClean.Gadgets.LookupProjection
import SP1CleanTest.Alignment.Support.BranchEnsembleFixture
import ToClean.Air.EnsembleCheck
import SP1CleanTest.Alignment.Support.BranchEnsembleVerifierLookups

/-! # Complete static lookup meanings of the branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- ByteXor's original static enumeration, also used internally by AND and OR providers. -/
def xorFixed : FiniteLookup Fp where
  table := (Gadgets.Xor.ByteXorTable (p := SP1Prime)).toRaw
  rows := List.ofFn fun (index : Fin (256 * 256)) =>
    let pair := ByteUtils.splitTwoBytes index
    toElements ((ByteUtils.fromByte pair.1, ByteUtils.fromByte pair.2,
      ByteUtils.fromByte (pair.1 ^^^ pair.2)) : fieldTriple Fp)
  realizes := by
    intro data row
    exact staticTable_realizes _ data row

/-- Full finite lookup meanings, including installed tables with no physical rows in this fixture. -/
def fixed (target : MemorySnapshot) : List (FiniteLookup Fp) :=
  let registers := FiniteLookup.ofStatic (target.registerTable (p := SP1Prime))
  let memory := FiniteLookup.ofStatic (target.memory.fixedTable (p := SP1Prime) (2 ^ 48))
  [FiniteLookup.ofStatic (source.sail.memorySnapshot.registerTable (p := SP1Prime)),
    FiniteLookup.ofStatic (source.sail.memory.fixedTable (p := SP1Prime) (2 ^ 48)),
    FiniteLookup.ofStatic (image.programTable (p := SP1Prime)), xorFixed,
    FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime)),
    FiniteLookup.ofStatic (image.writePermissionTable (p := SP1Prime)),
    FiniteLookup.ofStatic (HintQueue.sourceTable (p := SP1Prime) []),
    FiniteLookup.ofStatic (HintQueue.sourceWordTable (p := SP1Prime) []),
    { registers with table := { registers.table with name := "sp1.native.target_registers" } },
    { memory with table := { memory.table with name := "sp1.native.target_memory" } }]


/-- Static lookup indices for every installed component, including all currently empty providers. -/
def componentLookupIndices : List (List (Fin 10)) :=
  [[], [0], [1, 1, 1, 1, 1, 1, 1, 1], [], [], [], [], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3], [3], [3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [6], [7], [], [], [8], [9, 9, 9, 9, 9, 9, 9, 9]]

/-- Component selection keeps all installed physical slots and the fixed verifier at index zero. -/
abbrev componentAt (target : MemorySnapshot) (index : Fin 90) : Component Fp :=
  (assembly target).allTables[index.val]'(by change index.val < 90; exact index.isLt)

/-- The lookup rows promised for one installed component. -/
def fixedFor (target : MemorySnapshot) (index : Fin 90) : List (RawTable Fp) :=
  (componentLookupIndices[index.val]'(by change index.val < 90; exact index.isLt)).map fun table =>
    ((fixed target)[table.val]'(by change table.val < 10; exact table.isLt)).table

attribute [local circuit_norm]
  Gadgets.And.And8.circuit
  Gadgets.And.And8.main
  Gadgets.Conditional.circuit
  Gadgets.Conditional.main
  Gadgets.Equality.circuit
  Gadgets.Equality.main
  Gadgets.IsEqual.circuit
  Gadgets.IsEqual.main
  Gadgets.IsZero.circuit
  Gadgets.IsZero.main
  Gadgets.IsZeroField.circuit
  Gadgets.Or.Or8.circuit
  Gadgets.Or.Or8.main
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
  SP1Clean.DecodedProgramProvider.circuit
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
  SP1Clean.FixedProgramProvider.circuit
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


/-- Source-memory lookup naming is fixed independently of the sparse row inventory. -/
private theorem memory_table_name (memory : ByteMemory) (limit : ℕ) :
    (memory.fixedTable (p := SP1Prime) limit).name = "sp1.native.initial_memory" := by
  rw [ByteMemory.fixedTable]
  rfl

attribute [local circuit_norm] memory_table_name supportedChipFor RangeChip.circuitFor
  ProtectedStore.byte ProtectedStore.half ProtectedStore.word ProtectedStore.double
  DivRemChip.populateRow DivRemChip.constrainRow DivRemChip.assertZeros
  HostHintQueue.source HostHintQueue.sourceMain HostHintQueue.sourceWord HostHintQueue.sourceWordMain
  HostCommitBoundary.terminal HostCommitBoundary.terminalMain

-- Normalize proof-bearing wrappers only through their operation projection lemmas.
attribute [local circuit_norm] List.append_eq Component.rowOperations
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  GeneralFormalCircuit.WithHint.toSubcircuit_lookups FormalCircuit.toSubcircuit_lookups
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups
  Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits
  fixedFor componentLookupIndices fixed xorFixed FiniteLookup.ofStatic
  InitialMemoryLookup.circuitNamed InitialMemoryRead.circuitNamed
  OrderedFinalProvider.registerCircuit OrderedFinalProvider.ramCircuit

/-- The public verifier's dynamic target-change boundary contains interactions only. -/
private theorem lookup_slot_0 (target : MemorySnapshot) :
    (componentAt target 0).rowOperations.lookups.map (·.table) = fixedFor target 0 := by
  change (assembly target).verifierTable.rowOperations.lookups.map (·.table) = []
  rw [verifier_lookups]
  rfl

/-- Raw lookup identities at installed component 1 (verifier-inclusive index). -/
private theorem lookup_slot_1 (target : MemorySnapshot) :
    (componentAt target 1).rowOperations.lookups.map (·.table) = fixedFor target 1 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 2 (verifier-inclusive index). -/
private theorem lookup_slot_2 (target : MemorySnapshot) :
    (componentAt target 2).rowOperations.lookups.map (·.table) = fixedFor target 2 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]
  rfl

/-- Raw lookup identities at installed component 3 (verifier-inclusive index). -/
private theorem lookup_slot_3 (target : MemorySnapshot) :
    (componentAt target 3).rowOperations.lookups.map (·.table) = fixedFor target 3 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 4 (verifier-inclusive index). -/
private theorem lookup_slot_4 (target : MemorySnapshot) :
    (componentAt target 4).rowOperations.lookups.map (·.table) = fixedFor target 4 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 5 (verifier-inclusive index). -/
private theorem lookup_slot_5 (target : MemorySnapshot) :
    (componentAt target 5).rowOperations.lookups.map (·.table) = fixedFor target 5 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 6 (verifier-inclusive index). -/
private theorem lookup_slot_6 (target : MemorySnapshot) :
    (componentAt target 6).rowOperations.lookups.map (·.table) = fixedFor target 6 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 7 (verifier-inclusive index). -/
private theorem lookup_slot_7 (target : MemorySnapshot) :
    (componentAt target 7).rowOperations.lookups.map (·.table) = fixedFor target 7 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 8 (verifier-inclusive index). -/
private theorem lookup_slot_8 (target : MemorySnapshot) :
    (componentAt target 8).rowOperations.lookups.map (·.table) = fixedFor target 8 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 9 (verifier-inclusive index). -/
private theorem lookup_slot_9 (target : MemorySnapshot) :
    (componentAt target 9).rowOperations.lookups.map (·.table) = fixedFor target 9 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 10 (verifier-inclusive index). -/
private theorem lookup_slot_10 (target : MemorySnapshot) :
    (componentAt target 10).rowOperations.lookups.map (·.table) = fixedFor target 10 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 11 (verifier-inclusive index). -/
private theorem lookup_slot_11 (target : MemorySnapshot) :
    (componentAt target 11).rowOperations.lookups.map (·.table) = fixedFor target 11 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 12 (verifier-inclusive index). -/
private theorem lookup_slot_12 (target : MemorySnapshot) :
    (componentAt target 12).rowOperations.lookups.map (·.table) = fixedFor target 12 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 13 (verifier-inclusive index). -/
private theorem lookup_slot_13 (target : MemorySnapshot) :
    (componentAt target 13).rowOperations.lookups.map (·.table) = fixedFor target 13 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 14 (verifier-inclusive index). -/
private theorem lookup_slot_14 (target : MemorySnapshot) :
    (componentAt target 14).rowOperations.lookups.map (·.table) = fixedFor target 14 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 15 (verifier-inclusive index). -/
private theorem lookup_slot_15 (target : MemorySnapshot) :
    (componentAt target 15).rowOperations.lookups.map (·.table) = fixedFor target 15 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 16 (verifier-inclusive index). -/
private theorem lookup_slot_16 (target : MemorySnapshot) :
    (componentAt target 16).rowOperations.lookups.map (·.table) = fixedFor target 16 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 17 (verifier-inclusive index). -/
private theorem lookup_slot_17 (target : MemorySnapshot) :
    (componentAt target 17).rowOperations.lookups.map (·.table) = fixedFor target 17 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 18 (verifier-inclusive index). -/
private theorem lookup_slot_18 (target : MemorySnapshot) :
    (componentAt target 18).rowOperations.lookups.map (·.table) = fixedFor target 18 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 19 (verifier-inclusive index). -/
private theorem lookup_slot_19 (target : MemorySnapshot) :
    (componentAt target 19).rowOperations.lookups.map (·.table) = fixedFor target 19 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 20 (verifier-inclusive index). -/
private theorem lookup_slot_20 (target : MemorySnapshot) :
    (componentAt target 20).rowOperations.lookups.map (·.table) = fixedFor target 20 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 21 (verifier-inclusive index). -/
private theorem lookup_slot_21 (target : MemorySnapshot) :
    (componentAt target 21).rowOperations.lookups.map (·.table) = fixedFor target 21 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 22 (verifier-inclusive index). -/
private theorem lookup_slot_22 (target : MemorySnapshot) :
    (componentAt target 22).rowOperations.lookups.map (·.table) = fixedFor target 22 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 23 (verifier-inclusive index). -/
private theorem lookup_slot_23 (target : MemorySnapshot) :
    (componentAt target 23).rowOperations.lookups.map (·.table) = fixedFor target 23 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 24 (verifier-inclusive index). -/
private theorem lookup_slot_24 (target : MemorySnapshot) :
    (componentAt target 24).rowOperations.lookups.map (·.table) = fixedFor target 24 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 25 (verifier-inclusive index). -/
private theorem lookup_slot_25 (target : MemorySnapshot) :
    (componentAt target 25).rowOperations.lookups.map (·.table) = fixedFor target 25 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 26 (verifier-inclusive index). -/
private theorem lookup_slot_26 (target : MemorySnapshot) :
    (componentAt target 26).rowOperations.lookups.map (·.table) = fixedFor target 26 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 27 (verifier-inclusive index). -/
private theorem lookup_slot_27 (target : MemorySnapshot) :
    (componentAt target 27).rowOperations.lookups.map (·.table) = fixedFor target 27 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 28 (verifier-inclusive index). -/
private theorem lookup_slot_28 (target : MemorySnapshot) :
    (componentAt target 28).rowOperations.lookups.map (·.table) = fixedFor target 28 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 29 (verifier-inclusive index). -/
private theorem lookup_slot_29 (target : MemorySnapshot) :
    (componentAt target 29).rowOperations.lookups.map (·.table) = fixedFor target 29 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 30 (verifier-inclusive index). -/
private theorem lookup_slot_30 (target : MemorySnapshot) :
    (componentAt target 30).rowOperations.lookups.map (·.table) = fixedFor target 30 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 31 (verifier-inclusive index). -/
private theorem lookup_slot_31 (target : MemorySnapshot) :
    (componentAt target 31).rowOperations.lookups.map (·.table) = fixedFor target 31 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 32 (verifier-inclusive index). -/
private theorem lookup_slot_32 (target : MemorySnapshot) :
    (componentAt target 32).rowOperations.lookups.map (·.table) = fixedFor target 32 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 33 (verifier-inclusive index). -/
private theorem lookup_slot_33 (target : MemorySnapshot) :
    (componentAt target 33).rowOperations.lookups.map (·.table) = fixedFor target 33 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 34 (verifier-inclusive index). -/
private theorem lookup_slot_34 (target : MemorySnapshot) :
    (componentAt target 34).rowOperations.lookups.map (·.table) = fixedFor target 34 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 35 (verifier-inclusive index). -/
private theorem lookup_slot_35 (target : MemorySnapshot) :
    (componentAt target 35).rowOperations.lookups.map (·.table) = fixedFor target 35 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 36 (verifier-inclusive index). -/
private theorem lookup_slot_36 (target : MemorySnapshot) :
    (componentAt target 36).rowOperations.lookups.map (·.table) = fixedFor target 36 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 37 (verifier-inclusive index). -/
private theorem lookup_slot_37 (target : MemorySnapshot) :
    (componentAt target 37).rowOperations.lookups.map (·.table) = fixedFor target 37 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 38 (verifier-inclusive index). -/
private theorem lookup_slot_38 (target : MemorySnapshot) :
    (componentAt target 38).rowOperations.lookups.map (·.table) = fixedFor target 38 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 39 (verifier-inclusive index). -/
private theorem lookup_slot_39 (target : MemorySnapshot) :
    (componentAt target 39).rowOperations.lookups.map (·.table) = fixedFor target 39 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 40 (verifier-inclusive index). -/
private theorem lookup_slot_40 (target : MemorySnapshot) :
    (componentAt target 40).rowOperations.lookups.map (·.table) = fixedFor target 40 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 41 (verifier-inclusive index). -/
private theorem lookup_slot_41 (target : MemorySnapshot) :
    (componentAt target 41).rowOperations.lookups.map (·.table) = fixedFor target 41 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 42 (verifier-inclusive index). -/
private theorem lookup_slot_42 (target : MemorySnapshot) :
    (componentAt target 42).rowOperations.lookups.map (·.table) = fixedFor target 42 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 43 (verifier-inclusive index). -/
private theorem lookup_slot_43 (target : MemorySnapshot) :
    (componentAt target 43).rowOperations.lookups.map (·.table) = fixedFor target 43 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 44 (verifier-inclusive index). -/
private theorem lookup_slot_44 (target : MemorySnapshot) :
    (componentAt target 44).rowOperations.lookups.map (·.table) = fixedFor target 44 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 45 (verifier-inclusive index). -/
private theorem lookup_slot_45 (target : MemorySnapshot) :
    (componentAt target 45).rowOperations.lookups.map (·.table) = fixedFor target 45 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 46 (verifier-inclusive index). -/
private theorem lookup_slot_46 (target : MemorySnapshot) :
    (componentAt target 46).rowOperations.lookups.map (·.table) = fixedFor target 46 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 47 (verifier-inclusive index). -/
private theorem lookup_slot_47 (target : MemorySnapshot) :
    (componentAt target 47).rowOperations.lookups.map (·.table) = fixedFor target 47 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 48 (verifier-inclusive index). -/
private theorem lookup_slot_48 (target : MemorySnapshot) :
    (componentAt target 48).rowOperations.lookups.map (·.table) = fixedFor target 48 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 49 (verifier-inclusive index). -/
private theorem lookup_slot_49 (target : MemorySnapshot) :
    (componentAt target 49).rowOperations.lookups.map (·.table) = fixedFor target 49 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 50 (verifier-inclusive index). -/
private theorem lookup_slot_50 (target : MemorySnapshot) :
    (componentAt target 50).rowOperations.lookups.map (·.table) = fixedFor target 50 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 51 (verifier-inclusive index). -/
private theorem lookup_slot_51 (target : MemorySnapshot) :
    (componentAt target 51).rowOperations.lookups.map (·.table) = fixedFor target 51 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 52 (verifier-inclusive index). -/
private theorem lookup_slot_52 (target : MemorySnapshot) :
    (componentAt target 52).rowOperations.lookups.map (·.table) = fixedFor target 52 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 53 (verifier-inclusive index). -/
private theorem lookup_slot_53 (target : MemorySnapshot) :
    (componentAt target 53).rowOperations.lookups.map (·.table) = fixedFor target 53 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 54 (verifier-inclusive index). -/
private theorem lookup_slot_54 (target : MemorySnapshot) :
    (componentAt target 54).rowOperations.lookups.map (·.table) = fixedFor target 54 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 55 (verifier-inclusive index). -/
private theorem lookup_slot_55 (target : MemorySnapshot) :
    (componentAt target 55).rowOperations.lookups.map (·.table) = fixedFor target 55 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 56 (verifier-inclusive index). -/
private theorem lookup_slot_56 (target : MemorySnapshot) :
    (componentAt target 56).rowOperations.lookups.map (·.table) = fixedFor target 56 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 57 (verifier-inclusive index). -/
private theorem lookup_slot_57 (target : MemorySnapshot) :
    (componentAt target 57).rowOperations.lookups.map (·.table) = fixedFor target 57 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 58 (verifier-inclusive index). -/
private theorem lookup_slot_58 (target : MemorySnapshot) :
    (componentAt target 58).rowOperations.lookups.map (·.table) = fixedFor target 58 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 59 (verifier-inclusive index). -/
private theorem lookup_slot_59 (target : MemorySnapshot) :
    (componentAt target 59).rowOperations.lookups.map (·.table) = fixedFor target 59 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, Circuit.foldlRange.operations_eq, List.ofFn_succ]

/-- Raw lookup identities at installed component 60 (verifier-inclusive index). -/
private theorem lookup_slot_60 (target : MemorySnapshot) :
    (componentAt target 60).rowOperations.lookups.map (·.table) = fixedFor target 60 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 61 (verifier-inclusive index). -/
private theorem lookup_slot_61 (target : MemorySnapshot) :
    (componentAt target 61).rowOperations.lookups.map (·.table) = fixedFor target 61 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 62 (verifier-inclusive index). -/
private theorem lookup_slot_62 (target : MemorySnapshot) :
    (componentAt target 62).rowOperations.lookups.map (·.table) = fixedFor target 62 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 63 (verifier-inclusive index). -/
private theorem lookup_slot_63 (target : MemorySnapshot) :
    (componentAt target 63).rowOperations.lookups.map (·.table) = fixedFor target 63 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 64 (verifier-inclusive index). -/
private theorem lookup_slot_64 (target : MemorySnapshot) :
    (componentAt target 64).rowOperations.lookups.map (·.table) = fixedFor target 64 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 65 (verifier-inclusive index). -/
private theorem lookup_slot_65 (target : MemorySnapshot) :
    (componentAt target 65).rowOperations.lookups.map (·.table) = fixedFor target 65 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 66 (verifier-inclusive index). -/
private theorem lookup_slot_66 (target : MemorySnapshot) :
    (componentAt target 66).rowOperations.lookups.map (·.table) = fixedFor target 66 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 67 (verifier-inclusive index). -/
private theorem lookup_slot_67 (target : MemorySnapshot) :
    (componentAt target 67).rowOperations.lookups.map (·.table) = fixedFor target 67 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 68 (verifier-inclusive index). -/
private theorem lookup_slot_68 (target : MemorySnapshot) :
    (componentAt target 68).rowOperations.lookups.map (·.table) = fixedFor target 68 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 69 (verifier-inclusive index). -/
private theorem lookup_slot_69 (target : MemorySnapshot) :
    (componentAt target 69).rowOperations.lookups.map (·.table) = fixedFor target 69 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 70 (verifier-inclusive index). -/
private theorem lookup_slot_70 (target : MemorySnapshot) :
    (componentAt target 70).rowOperations.lookups.map (·.table) = fixedFor target 70 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 71 (verifier-inclusive index). -/
private theorem lookup_slot_71 (target : MemorySnapshot) :
    (componentAt target 71).rowOperations.lookups.map (·.table) = fixedFor target 71 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 72 (verifier-inclusive index). -/
private theorem lookup_slot_72 (target : MemorySnapshot) :
    (componentAt target 72).rowOperations.lookups.map (·.table) = fixedFor target 72 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 73 (verifier-inclusive index). -/
private theorem lookup_slot_73 (target : MemorySnapshot) :
    (componentAt target 73).rowOperations.lookups.map (·.table) = fixedFor target 73 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 74 (verifier-inclusive index). -/
private theorem lookup_slot_74 (target : MemorySnapshot) :
    (componentAt target 74).rowOperations.lookups.map (·.table) = fixedFor target 74 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 75 (verifier-inclusive index). -/
private theorem lookup_slot_75 (target : MemorySnapshot) :
    (componentAt target 75).rowOperations.lookups.map (·.table) = fixedFor target 75 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 76 (verifier-inclusive index). -/
private theorem lookup_slot_76 (target : MemorySnapshot) :
    (componentAt target 76).rowOperations.lookups.map (·.table) = fixedFor target 76 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 77 (verifier-inclusive index). -/
private theorem lookup_slot_77 (target : MemorySnapshot) :
    (componentAt target 77).rowOperations.lookups.map (·.table) = fixedFor target 77 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 78 (verifier-inclusive index). -/
private theorem lookup_slot_78 (target : MemorySnapshot) :
    (componentAt target 78).rowOperations.lookups.map (·.table) = fixedFor target 78 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 79 (verifier-inclusive index). -/
private theorem lookup_slot_79 (target : MemorySnapshot) :
    (componentAt target 79).rowOperations.lookups.map (·.table) = fixedFor target 79 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 80 (verifier-inclusive index). -/
private theorem lookup_slot_80 (target : MemorySnapshot) :
    (componentAt target 80).rowOperations.lookups.map (·.table) = fixedFor target 80 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 81 (verifier-inclusive index). -/
private theorem lookup_slot_81 (target : MemorySnapshot) :
    (componentAt target 81).rowOperations.lookups.map (·.table) = fixedFor target 81 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 82 (verifier-inclusive index). -/
private theorem lookup_slot_82 (target : MemorySnapshot) :
    (componentAt target 82).rowOperations.lookups.map (·.table) = fixedFor target 82 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 83 (verifier-inclusive index). -/
private theorem lookup_slot_83 (target : MemorySnapshot) :
    (componentAt target 83).rowOperations.lookups.map (·.table) = fixedFor target 83 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 84 (verifier-inclusive index). -/
private theorem lookup_slot_84 (target : MemorySnapshot) :
    (componentAt target 84).rowOperations.lookups.map (·.table) = fixedFor target 84 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 85 (verifier-inclusive index). -/
private theorem lookup_slot_85 (target : MemorySnapshot) :
    (componentAt target 85).rowOperations.lookups.map (·.table) = fixedFor target 85 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 86 (verifier-inclusive index). -/
private theorem lookup_slot_86 (target : MemorySnapshot) :
    (componentAt target 86).rowOperations.lookups.map (·.table) = fixedFor target 86 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 87 (verifier-inclusive index). -/
private theorem lookup_slot_87 (target : MemorySnapshot) :
    (componentAt target 87).rowOperations.lookups.map (·.table) = fixedFor target 87 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at installed component 88 (verifier-inclusive index). -/
private theorem lookup_slot_88 (target : MemorySnapshot) :
    (componentAt target 88).rowOperations.lookups.map (·.table) = fixedFor target 88 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]
  rfl

/-- Raw lookup identities at installed component 89 (verifier-inclusive index). -/
private theorem lookup_slot_89 (target : MemorySnapshot) :
    (componentAt target 89).rowOperations.lookups.map (·.table) = fixedFor target 89 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]
  rfl

/-- Each installed component has exactly its listed fixed-table predicates. -/
theorem lookup_slot (target : MemorySnapshot) (index : Fin 90) :
    (componentAt target index).rowOperations.lookups.map (·.table) = fixedFor target index := by
  fin_cases index
  · exact lookup_slot_0 target
  · exact lookup_slot_1 target
  · exact lookup_slot_2 target
  · exact lookup_slot_3 target
  · exact lookup_slot_4 target
  · exact lookup_slot_5 target
  · exact lookup_slot_6 target
  · exact lookup_slot_7 target
  · exact lookup_slot_8 target
  · exact lookup_slot_9 target
  · exact lookup_slot_10 target
  · exact lookup_slot_11 target
  · exact lookup_slot_12 target
  · exact lookup_slot_13 target
  · exact lookup_slot_14 target
  · exact lookup_slot_15 target
  · exact lookup_slot_16 target
  · exact lookup_slot_17 target
  · exact lookup_slot_18 target
  · exact lookup_slot_19 target
  · exact lookup_slot_20 target
  · exact lookup_slot_21 target
  · exact lookup_slot_22 target
  · exact lookup_slot_23 target
  · exact lookup_slot_24 target
  · exact lookup_slot_25 target
  · exact lookup_slot_26 target
  · exact lookup_slot_27 target
  · exact lookup_slot_28 target
  · exact lookup_slot_29 target
  · exact lookup_slot_30 target
  · exact lookup_slot_31 target
  · exact lookup_slot_32 target
  · exact lookup_slot_33 target
  · exact lookup_slot_34 target
  · exact lookup_slot_35 target
  · exact lookup_slot_36 target
  · exact lookup_slot_37 target
  · exact lookup_slot_38 target
  · exact lookup_slot_39 target
  · exact lookup_slot_40 target
  · exact lookup_slot_41 target
  · exact lookup_slot_42 target
  · exact lookup_slot_43 target
  · exact lookup_slot_44 target
  · exact lookup_slot_45 target
  · exact lookup_slot_46 target
  · exact lookup_slot_47 target
  · exact lookup_slot_48 target
  · exact lookup_slot_49 target
  · exact lookup_slot_50 target
  · exact lookup_slot_51 target
  · exact lookup_slot_52 target
  · exact lookup_slot_53 target
  · exact lookup_slot_54 target
  · exact lookup_slot_55 target
  · exact lookup_slot_56 target
  · exact lookup_slot_57 target
  · exact lookup_slot_58 target
  · exact lookup_slot_59 target
  · exact lookup_slot_60 target
  · exact lookup_slot_61 target
  · exact lookup_slot_62 target
  · exact lookup_slot_63 target
  · exact lookup_slot_64 target
  · exact lookup_slot_65 target
  · exact lookup_slot_66 target
  · exact lookup_slot_67 target
  · exact lookup_slot_68 target
  · exact lookup_slot_69 target
  · exact lookup_slot_70 target
  · exact lookup_slot_71 target
  · exact lookup_slot_72 target
  · exact lookup_slot_73 target
  · exact lookup_slot_74 target
  · exact lookup_slot_75 target
  · exact lookup_slot_76 target
  · exact lookup_slot_77 target
  · exact lookup_slot_78 target
  · exact lookup_slot_79 target
  · exact lookup_slot_80 target
  · exact lookup_slot_81 target
  · exact lookup_slot_82 target
  · exact lookup_slot_83 target
  · exact lookup_slot_84 target
  · exact lookup_slot_85 target
  · exact lookup_slot_86 target
  · exact lookup_slot_87 target
  · exact lookup_slot_88 target
  · exact lookup_slot_89 target

/-- Actual lookup predicates, not just names, agree with the finite realization inventory. -/
theorem component_lookups (target : MemorySnapshot) :
    (assembly target).allTables.map (fun component => component.rowOperations.lookups.map (·.table)) =
      componentLookupIndices.map (fun indices => indices.map fun index =>
        ((fixed target)[index.val]'(by change index.val < 10; exact index.isLt)).table) := by
  apply List.ext_getElem
  · simp only [List.length_map]
    rfl
  intro index bound otherBound
  simp only [List.getElem_map]
  have indexBound := otherBound
  change index < 90 at indexBound
  exact lookup_slot target ⟨index, indexBound⟩

/-- Every installed static lookup has an authenticated finite realization by table identity. -/
theorem lookups_complete (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).allTables) (lookup : Lookup Fp)
    (used : lookup ∈ component.rowOperations.lookups) :
    ∃ fixedTable ∈ fixed target, fixedTable.table = lookup.table := by
  have present := List.mem_map_of_mem
    (f := fun component : Component Fp => component.rowOperations.lookups.map (·.table)) member
  rw [component_lookups] at present
  obtain ⟨indices, _, equal⟩ := List.mem_map.mp present
  have lookupPresent := List.mem_map_of_mem (f := fun lookup : Lookup Fp => lookup.table) used
  rw [← equal] at lookupPresent
  obtain ⟨index, _, tableEqual⟩ := List.mem_map.mp lookupPresent
  exact ⟨(fixed target)[index.val], List.getElem_mem _, tableEqual⟩


end SP1Clean.Audit.BranchEnsemble
