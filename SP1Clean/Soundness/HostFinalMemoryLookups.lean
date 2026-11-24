import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.LocalCoreLookups

/-! # The complete-memory host assembly is lookup-free

Every installed provider and handler uses AIR constraints and channels; no lookup remains,
including in currently unused physical slots. Constraints therefore depend on a row's cells
alone, so they survive any change of canonical prover data, such as forgetting an appended fixed
provider. Lookup freedom is proved once per building block over any admissible field: the local
core, the protected stores, the HostCall ledger, the receivers and resources, the target checks,
the HALT padding replacement and the two receipt installations.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat SP1Clean SP1Clean.Semantics SP1Clean.Soundness SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

-- The host leaves normalize their rows through these circuits and readers.
attribute [local circuit_norm]
  AddrAddOperation.circuit AddrAddOperation.main AddressDiv8.circuit AddressDiv8.main
  AddressOperation.circuit AddressOperation.main AddressOrder.circuit AddressOrder.main
  BoundedWord.circuit BoundedWord.main Circuit.Guarded.circuit ClockOrder.circuit ClockOrder.main
  CoreSyscallChip.circuit CoreSyscallChip.main Gadgets.Equality.circuit Gadgets.Equality.main
  Gadgets.IsZeroField.circuit HaltChip.circuit HaltChip.main HaltPaddingChip.circuit
  HaltPaddingChip.main HintReadSpan.circuit HintReadSpan.main HintReadStep.circuit
  HintReadStep.main HintReadWordChip.circuit HintReadWordChip.main HostCallChip.circuit
  HostCallChip.main HostCommitChip.circuit HostCommitChip.main HostNoopChip.circuit
  HostNoopChip.main HostHaltChip.circuit HostHaltChip.main HostHintLengthChip.circuit
  HostHintLengthChip.main HostHintReadChip.circuit HostHintReadChip.main
  LtOperationUnsigned.circuit LtOperationUnsigned.main Readers.CPUState.circuit
  Readers.CPUState.main Readers.ITypeReaderImmutable.circuit Readers.ITypeReaderImmutable.main
  Readers.MemoryAccess.circuit Readers.MemoryAccess.main Readers.RegisterAccessCols.circuit
  Readers.RegisterAccessCols.main Readers.RegisterAccessTimestamp.circuit
  Readers.RegisterAccessTimestamp.main
  StoreByteChip.circuit StoreByteChip.main StoreDoubleChip.circuit StoreDoubleChip.main
  StoreHalfChip.circuit StoreHalfChip.main StoreWordChip.circuit StoreWordChip.main
  SyscallCodeGuard.circuit SyscallCodeGuard.main U16CompareOperation.circuit
  U16CompareOperation.main WordRangeCheck.circuit WordRangeCheck.main

attribute [local circuit_norm] ProtectedStore.byte ProtectedStore.half ProtectedStore.word
  ProtectedStore.double HostHintQueue.source HostHintQueue.sourceWord
  StaticTable.payloadComponent StaticTable.payloadProvider
  HostCommitBoundary.terminal HostCommitBoundary.terminalMain
  WritePermissionProvider.component WritePermissionProvider.membershipComponent
  ProgramImage.writePermissionTable StaticTable.component HostCallLedger.producer
  HostCallReceivers.halt HostCallReceivers.noop HostCallReceivers.commit
  HostCallReceivers.hintLength HostHintReadHandoff.receiver HostHintReadCoverage.handler
  HintReadCoverage.view HintReadCoverage.component HaltPaddingChip.component

-- Normalize proof-bearing wrappers only through their operation projection lemmas.
attribute [local circuit_norm] List.append_eq Component.rowOperations
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  GeneralFormalCircuit.WithHint.toSubcircuit_lookups FormalCircuit.toSubcircuit_lookups
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups
  Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits

/-- Normalize a host component's row to its (empty) lookup list. -/
local macro "row_lookups" : tactic =>
  `(tactic| (rw [Component.lookups_eq]; simp [circuit_norm, Circuit.foldlRange.operations_eq,
    List.ofFn_succ, StaticTable.provider]))

/-- The permission-checked stores and the write-permission provider pair are lookup-free. -/
theorem protectedTables_lookupFree (image : ProgramImage) (source : ExecutionSnapshot) :
    LookupFree (ProtectedLocalCore.tables (p := p) image source) := by
  unfold ProtectedLocalCore.tables
  refine LookupFree.append
    (((((LocalCore.tables_lookupFree image source).set ?_ _).set ?_ _).set ?_ _).set ?_ _) ?_
  any_goals row_lookups
  simp only [LookupFree.cons_iff, LookupFree.nil, and_true]
  exact ⟨by row_lookups, by row_lookups⟩

/-- The host wrapper replaces the syscall table by the lookup-free HostCall ledger. -/
theorem hostTables_lookupFree (image : ProgramImage) (source : ExecutionSnapshot)
    {auxiliary : List (Component (ZMod p))} (free : LookupFree auxiliary) :
    LookupFree (HostLocalCore.tables image source auxiliary) :=
  ((protectedTables_lookupFree image source).set (by row_lookups) _).append free

private theorem noop_lookupFree (includeVerify : Bool) :
    (HostCallReceivers.profileNoop (p := p) includeVerify).component.operations.lookups = [] := by
  rw [Component.lookups_eq]
  cases includeVerify with
  | false =>
    change ((HostNoopChip.main .enter (varFromOffset HostNoopChip.Inputs (F := ZMod p) 0)).operations
      (size HostNoopChip.Inputs)).lookups = []
    simp [circuit_norm]
  | true =>
    change ((HostNoopChip.choiceMain (varFromOffset HostNoopChip.Inputs (F := ZMod p) 0)).operations
      (size HostNoopChip.Inputs)).lookups = []
    simp [HostNoopChip.choiceMain, circuit_norm]

/-- Every implemented control, commitment and HINT_LEN receiver is lookup-free. -/
theorem available_lookupFree (includeVerify : Bool := true) :
    LookupFree ((HostCallReceivers.availableFor (p := p) includeVerify).map (·.component)) := by
  apply LookupFree.map
  intro view member
  simp only [HostCallReceivers.availableFor, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false] at member
  rcases member with (((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩) | rfl | rfl
  · row_lookups
  · exact noop_lookupFree includeVerify
  · row_lookups
  · row_lookups
  · rw [Component.lookups_eq]
    exact Guarded.main_lookups (HostHintLengthChip.circuit false) inferInstance _ _
  · rw [Component.lookups_eq]
    exact Guarded.main_lookups (HostHintLengthChip.circuit true) inferInstance _ _

/-- The ordinary observation consumer and its three terminals are lookup-free. -/
theorem observation_lookupFree : LookupFree (Soundness.OrdinaryObservation.tables (p := p)) := by
  simp only [Soundness.OrdinaryObservation.tables, LookupFree.cons_iff, LookupFree.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Component.lookups_eq]
    exact Guarded.main_lookups OrdinaryObservation.circuit OrdinaryObservation.guardSupported _ _
  all_goals rw [Component.lookups_eq]
  all_goals
    simp [Soundness.OrdinaryObservation.terminalComponent, OrdinaryObservation.terminal,
      OrdinaryObservation.terminalEmpty, OrdinaryObservation.terminalNonempty,
      OrdinaryObservation.terminalAny, OrdinaryObservation.emptyMain,
      OrdinaryObservation.nonemptyMain, OrdinaryObservation.anyMain, Gadgets.Equality.main, assertBool,
      Gadgets.IsZeroField.circuit, circuit_norm, List.ofFn_succ]

/-- The HINT_READ handler, every other receiver, the word consumers and the source resources. -/
theorem registered_lookupFree (hints : List Bytes) :
    LookupFree ((HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.available).map
      (·.component) ++
        (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources hints)) := by
  refine LookupFree.append (LookupFree.cons ?_ available_lookupFree) ?_
  · rw [Component.lookups_eq]
    exact Guarded.main_lookups HostHintReadChip.circuit inferInstance _ _
  simp only [HostHintReadLocal.sourceResources, ← List.append_assoc]
  refine LookupFree.append ?_ observation_lookupFree
  simp only [HostHintReadHandoff.wordResources, HostHintReadLocal.bankResources, List.cons_append,
    List.nil_append, LookupFree.cons_iff, LookupFree.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals row_lookups

/-- The complete-memory host assembly is lookup-free whenever its handler and resource block is. -/
theorem ensemble_lookupFree {image : ProgramImage} {source : ExecutionSnapshot}
    {target : MemorySnapshot} {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    {names : UniqueNames image source (FinalMemoryChecks.checkTables target) others resources}
    {registration : Registration image source (FinalMemoryChecks.checkTables target) others resources channels}
    (free : LookupFree ((HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))) :
    LookupFree (ensemble image source target final bankFinal others resources channels names
      registration).tables := by
  change LookupFree (withReceipts image source target final bankFinal others resources channels
    names registration).tables
  refine FinalReceiptEnsemble.install_lookupFree (FinalReceiptEnsemble.install_lookupFree ?_)
  rw [base_tables_eq]
  exact LookupFree.set (LookupFree.append (hostTables_lookupFree image source free)
    (FinalMemoryChecks.checkTables_lookupFree target)) (by row_lookups) _

/-- Every installed component is lookup-free, including currently unused physical slots. -/
theorem installed_lookupFree {image : ProgramImage} {source : ExecutionSnapshot}
    {target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)} :
    LookupFree (Installed image source target final).tables :=
  ensemble_lookupFree (registered_lookupFree source.host.io.hints)

end SP1Clean.Soundness.HostFinalMemory
