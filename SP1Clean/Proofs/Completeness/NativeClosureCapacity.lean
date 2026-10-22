import SP1Clean.Proofs.Completeness.NativeBaseTrace
import SP1Clean.Proofs.Completeness.CanonicalClosure
import SP1Clean.Proofs.Completeness.PhysicalFootprint

/-! # Physical capacity of native provider closure

Canonical recount emits at most one row per selected consumer key. The checked compiler's
existing semantic row limit therefore bounds every recounted provider table. The estimates below
are internal proofs of UInt64 representability, never additional admission conditions; exact
channel and physical resource accounting remains in `PhysicalFootprint`.

Normalize circuit interaction counts separately so large instruction families do not consume
one shared elaboration budget. The public theorem takes no readiness or footprint premise.
-/

namespace SP1Clean.Soundness

open Air.Flat

section InteractionCounts

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance nativeClosureCapacityFieldBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
attribute [local circuit_norm]
  AddChip.main Readers.CPUState.circuit Readers.CPUState.main
  Readers.RTypeReader.circuit Readers.RTypeReader.main Readers.RegisterWrite.circuit
  Readers.RegisterWrite.main Readers.RegisterAccessCols.circuit Readers.RegisterAccessCols.main
  Readers.RegisterAccessTimestamp.circuit Readers.RegisterAccessTimestamp.main AddOperation.circuit
  AddOperation.main Gadgets.Equality.main FormalAssertion.toSubcircuit_interactions
  GeneralFormalCircuit.toSubcircuit_interactions AddiChip.main Readers.ITypeReader.circuit
  Readers.ITypeReader.main AddwChip.main Readers.ALUTypeReader.circuit
  Readers.ALUTypeReader.main AddwOperation.circuit AddwOperation.main
  U16MSBOperation.circuit U16MSBOperation.main SubChip.main
  SubOperation.circuit SubOperation.main SubwChip.main
  SubwOperation.circuit SubwOperation.main BitwiseChip.main
  BitwiseU16Operation.circuit BitwiseU16Operation.main BitwiseOperation.circuit
  BitwiseOperation.main LtChip.main LtOperationSigned.circuit
  LtOperationSigned.main LtOperationUnsigned.circuit LtOperationUnsigned.main
  U16CompareOperation.circuit U16CompareOperation.main ShiftLeftChip.main
  ShiftLeftCore.circuit ShiftLeftCore.main ShiftRightChip.main
  ShiftRightCore.circuit ShiftRightCore.main JalChip.main
  Readers.JTypeReader.circuit Readers.JTypeReader.main JalrChip.main
  BranchChip.main Readers.ITypeReaderImmutable.circuit Readers.ITypeReaderImmutable.main
  UTypeChip.main LoadByteChip.main AddressOperation.circuit
  AddressOperation.main AddrAddOperation.circuit AddrAddOperation.main
  Readers.MemoryAccess.circuit Readers.MemoryAccess.main LoadHalfChip.main
  LoadWordChip.main LoadDoubleChip.main LoadX0Chip.main
  StoreByteChip.main StoreHalfChip.main StoreWordChip.main
  StoreDoubleChip.main MulChip.main MulOperation.circuit
  MulOperation.main U16toU8OperationSafe.circuit U16toU8OperationSafe.main
  DivRemChip.main DivRemChip.populateRow DivRemChip.constrainRow
  DivRemCompare.circuit DivRemCompare.main DivRemCore.circuit
  DivRemCore.main IsEqualWordOperation.circuit IsEqualWordOperation.main
  IsZeroWordOperation.circuit IsZeroWordOperation.main IsZeroOperation.circuit
  IsZeroOperation.main DivRemChip.assertZeros AluX0Chip.main
  Readers.ALUTypeReaderImmutable.circuit Readers.ALUTypeReaderImmutable.main BranchChip.circuit

private theorem add_interactionBound :
    ({ circuit := AddChip.circuit (p := p),
        Assumptions := (AddChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem addi_interactionBound :
    ({ circuit := AddiChip.circuit (p := p),
        Assumptions := (AddiChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem addw_interactionBound :
    ({ circuit := AddwChip.circuit (p := p),
        Assumptions := (AddwChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem sub_interactionBound :
    ({ circuit := SubChip.circuit (p := p),
        Assumptions := (SubChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem subw_interactionBound :
    ({ circuit := SubwChip.circuit (p := p),
        Assumptions := (SubwChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem bitwise_interactionBound :
    ({ circuit := BitwiseChip.circuit (p := p),
        Assumptions := (BitwiseChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem lt_interactionBound :
    ({ circuit := LtChip.circuit (p := p),
        Assumptions := (LtChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem shiftLeft_interactionBound :
    ({ circuit := ShiftLeftChip.circuit (p := p),
        Assumptions := (ShiftLeftChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem shiftRight_interactionBound :
    ({ circuit := ShiftRightChip.circuit (p := p),
        Assumptions := (ShiftRightChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem jal_interactionBound :
    ({ circuit := JalChip.circuit (p := p),
        Assumptions := (JalChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem jalr_interactionBound :
    ({ circuit := JalrChip.circuit (p := p),
        Assumptions := (JalrChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem branch_interactionBound :
    ({ circuit := BranchChip.circuit (p := p),
        Assumptions := (BranchChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem uType_interactionBound :
    ({ circuit := UTypeChip.circuit (p := p),
        Assumptions := (UTypeChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem loadByte_interactionBound :
    ({ circuit := LoadByteChip.circuit (p := p),
        Assumptions := (LoadByteChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem loadHalf_interactionBound :
    ({ circuit := LoadHalfChip.circuit (p := p),
        Assumptions := (LoadHalfChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem loadWord_interactionBound :
    ({ circuit := LoadWordChip.circuit (p := p),
        Assumptions := (LoadWordChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem loadDouble_interactionBound :
    ({ circuit := LoadDoubleChip.circuit (p := p),
        Assumptions := (LoadDoubleChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem loadX0_interactionBound :
    ({ circuit := LoadX0Chip.circuit (p := p),
        Assumptions := (LoadX0Chip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem storeByte_interactionBound :
    ({ circuit := StoreByteChip.circuit (p := p),
        Assumptions := (StoreByteChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem storeHalf_interactionBound :
    ({ circuit := StoreHalfChip.circuit (p := p),
        Assumptions := (StoreHalfChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem storeWord_interactionBound :
    ({ circuit := StoreWordChip.circuit (p := p),
        Assumptions := (StoreWordChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem storeDouble_interactionBound :
    ({ circuit := StoreDoubleChip.circuit (p := p),
        Assumptions := (StoreDoubleChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem mul_interactionBound :
    ({ circuit := MulChip.circuit (p := p),
        Assumptions := (MulChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem divRem_interactionBound :
    ({ circuit := DivRemChip.circuit (p := p),
        Assumptions := (DivRemChip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem aluX0_interactionBound :
    ({ circuit := AluX0Chip.circuit (p := p),
        Assumptions := (AluX0Chip.circuit (p := p)).Assumptions } : Component (ZMod p)).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [Component.interactions_eq, circuit_norm]
  norm_num

private theorem instructionInteractionBound (id : InstructionChipId) :
    (supportedChipFor (p := p) id).table.operations.interactions.length ≤ 2 ^ 16 := by
  cases id with
  | add => exact add_interactionBound
  | addi => exact addi_interactionBound
  | addw => exact addw_interactionBound
  | sub => exact sub_interactionBound
  | subw => exact subw_interactionBound
  | bitwise => exact bitwise_interactionBound
  | lt => exact lt_interactionBound
  | shiftLeft => exact shiftLeft_interactionBound
  | shiftRight => exact shiftRight_interactionBound
  | jal => exact jal_interactionBound
  | jalr => exact jalr_interactionBound
  | branch => exact branch_interactionBound
  | uType => exact uType_interactionBound
  | loadByte => exact loadByte_interactionBound
  | loadHalf => exact loadHalf_interactionBound
  | loadWord => exact loadWord_interactionBound
  | loadDouble => exact loadDouble_interactionBound
  | loadX0 => exact loadX0_interactionBound
  | storeByte => exact storeByte_interactionBound
  | storeHalf => exact storeHalf_interactionBound
  | storeWord => exact storeWord_interactionBound
  | storeDouble => exact storeDouble_interactionBound
  | mul => exact mul_interactionBound
  | divRem => exact divRem_interactionBound
  | aluX0 => exact aluX0_interactionBound



attribute [local circuit_norm]
  Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits Gadgets.ToBits.main
  MemoryProviderChip.circuit MemoryProviderChip.main WordRangeCheck.circuit WordRangeCheck.main
  MemoryFinalizeChip.circuit MemoryFinalizeChip.main MemoryBumpChip.main
  StateBumpChip.main HaltChip.circuit HaltChip.main
  SyscallInstrsChip.circuit SyscallInstrsChip.main

private theorem suffixInteractionBound (id : ProviderTableId)
    (member : id ∈ [.memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt]) :
    (Soundness.providerTableFor (p := p) id).operations.interactions.length ≤ 2 ^ 16 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Soundness.providerTableFor, Component.interactions_eq, circuit_norm] <;> norm_num

private theorem verifierInteractionBound :
    (sp1Ensemble (p := p)).verifierOperations.interactions.length ≤ 2 ^ 16 := by
  change ((sp1StateVerifierProgram (p := p)).main
    (varFromOffset SP1PublicIO 0)).circuitOperations.interactions.length ≤ _
  simp only [sp1StateVerifierProgram, Verifier.ofInteractions_interactions]
  simp [sp1StateVerifierMain, circuit_norm]


end InteractionCounts

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

open SupportedCoreTraceWitness

omit [Fact (2 ^ 25 < p)] in
private theorem tableLedgerLength (table : Table (ZMod p)) :
    (tableCleanAccesses table).length =
      table.length * table.component.operations.interactions.length := by
  simp only [tableCleanAccesses, List.length_map, Table.interactions_length]

omit [Fact (2 ^ 25 < p)] in
private theorem tableFamilyLength {ι : Type} (ids : List ι) (table : ι → Table (ZMod p))
    (bound : ℕ) (bounded : ∀ id ∈ ids, (tableCleanAccesses (table id)).length ≤ bound) :
    (tablesCleanAccesses (ids.map table)).length ≤ ids.length * bound := by
  simp only [tablesCleanAccesses, List.flatMap_map, List.length_flatMap]
  simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using
    List.sum_le_card_nsmul (ids.map fun id => (tableCleanAccesses (table id)).length) bound
      (by simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using bounded)

private theorem skeletonLengthBound (trace : SupportedCoreTraceWitness p) (rows : ℕ)
    (instructions : ∀ id, (trace.instructionEvents id).length ≤ rows)
    (providers : ∀ id ∈ [.memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt],
      trace.providerHeight id ≤ rows) :
    trace.skeletonLedger.length ≤ (1 + 30 * rows) * 2 ^ 16 := by
  have instructionCost (id : InstructionChipId) :
      (tableCleanAccesses (trace.instructionTableFor id)).length ≤ rows * 2 ^ 16 := by
    rw [tableLedgerLength, instructionTableFor_length, instructionTableFor_component]
    exact Nat.mul_le_mul (instructions id) (instructionInteractionBound id)
  have providerCost (id : ProviderTableId)
      (member : id ∈ [.memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt]) :
      (tableCleanAccesses (trace.providerTableFor id)).length ≤ rows * 2 ^ 16 := by
    rw [tableLedgerLength, providerTableFor_length, providerTableFor_component]
    exact Nat.mul_le_mul (providers id member) (suffixInteractionBound id member)
  have instructionBound := tableFamilyLength InstructionChipId.all trace.instructionTableFor
    (rows * 2 ^ 16) (fun id _ => instructionCost id)
  have providerBound := tableFamilyLength
    [.memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt] trace.providerTableFor
    (rows * 2 ^ 16) providerCost
  have syscallEmpty : (tableCleanAccesses (trace.providerTableFor .syscallInstrs)).length = 0 := by
    rw [tableLedgerLength, providerTableFor_length]
    simp only [providerHeight, Nat.zero_mul]
  have verifierBound : trace.verifierLedger.length ≤ 2 ^ 16 := by
    simpa only [verifierLedger, Operations.interactionValues, List.length_map] using
      (verifierInteractionBound (p := p))
  rw [skeletonLedger, List.length_append, skeletonTables, tables_take_instructionTables,
    tables_drop_preprocessed, providerTables_drop_preprocessed, tablesCleanAccesses_append,
    List.length_append]
  change (tablesCleanAccesses trace.instructionTables).length ≤ 25 * (rows * 2 ^ 16) at instructionBound
  simp only [List.map_cons, List.map_nil, tablesCleanAccesses_cons,
    tablesCleanAccesses_nil, List.length_append, List.length_cons, List.length_nil] at providerBound ⊢
  omega


open TraceGen Execution

private theorem nativeProviderHeightBound (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) (id : ProviderTableId)
    (member : id ∈ [.memoryInit, .memoryFinalize, .memoryBump, .stateBump, .halt]) :
    (nativeBaseTrace statement execution).providerHeight id ≤
      6 * Model.Core.Profile.maxOrdinaryTransitions + 1 := by
  let compiled := compileExecution statement.program execution (nativeInitialClock statement)
  have bounded := compileExecution_rows_length_le_limit statement.program execution (nativeInitialClock statement)
  have schedules := compileExecution_schedule_lengths statement.program execution (nativeInitialClock statement)
  have historyBound := compiled.memoryHistory_length_le schedules
  have memoryBumps := compiled.memoryBumps_length_le schedules
  have boundaries := memoryBoundaryEntries_length_le compiled.memoryHistory
  have stateBumps := stateBumpEvents_length_le compiled.routedEvents
  rw [show compiled.routedEvents.length = compiled.rows.length from List.length_map _] at stateBumps
  change compiled.rows.length ≤ Model.Core.Profile.maxOrdinaryTransitions at bounded
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · change (memoryInitialEntries compiled.memoryHistory).length ≤ _
    omega
  · change (memoryFinalEntries compiled.memoryHistory).length ≤ _
    omega
  · change compiled.memoryBumps.length ≤ _
    omega
  · change (stateBumpEvents compiled.routedEvents).length ≤ _
    omega
  · change 1 ≤ 6 * Model.Core.Profile.maxOrdinaryTransitions + 1
    omega

/-- Native provider recount fits Clean's physical table index without a new caller premise. -/
theorem nativeBaseTrace_canonicalCapacity (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) :
    (nativeBaseTrace statement execution).CanonicalCapacity := by
  apply canonicalCapacity_of_closingKeyList
  have keys : (nativeBaseTrace statement execution).closingKeyList.length ≤
      (nativeBaseTrace statement execution).skeletonLedger.length := by
    unfold closingKeyList LookupAccessList.closingKeys LookupAccessList.active
    exact (List.dedup_sublist _).length_le.trans
      ((List.length_filter_le _ _).trans ((List.length_map _).le.trans (List.length_filter_le _ _)))
  have skeleton := skeletonLengthBound (nativeBaseTrace statement execution)
    (6 * Model.Core.Profile.maxOrdinaryTransitions + 1)
    (fun id => ?_) (nativeProviderHeightBound statement execution)
  · exact keys.trans (skeleton.trans (by decide))
  · have events := CompiledExecution.instructionEvents_length_le
      (compileExecution statement.program execution (nativeInitialClock statement)) id
    have bounded := compileExecution_rows_length_le_limit statement.program execution (nativeInitialClock statement)
    change (compileExecution statement.program execution (nativeInitialClock statement)).rows.length ≤ Model.Core.Profile.maxOrdinaryTransitions at bounded
    change ((compileExecution statement.program execution (nativeInitialClock statement)).instructionEvents id).length ≤ _
    omega

end SP1Clean.Soundness
