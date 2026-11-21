import SP1Clean.Export.FixedHintAssembly
import SP1Clean.Native.Operations.HostHintQueueTerminal
import ToClean.Air.EnsembleCheck
import ToClean.Air.ProverInputStatement
import ToClean.Circuit.SubcircuitProjection

/-! # Installed assembly with a private timestamp at the target hint queue

The final hint clock lives in the last physical table. Both queue pointers come from the
authenticated snapshots. The fixed-clock host proof can be reused at the timestamp read from
that physical table.
-/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Soundness Semantics

/-- The pinned supervisor field. -/
abbrev Fp := FixedHintAssembly.Fp

/-- Public assembly data sufficient to specify both boundaries of a local segment. -/
structure Context where
  /-- Committed SP1 program and initial byte image. -/
  image : ProgramImage
  /-- Complete authenticated incoming Sail, host and clock snapshot. -/
  source : ExecutionSnapshot
  /-- Complete authenticated outgoing Sail, host and clock snapshot. -/
  target : ExecutionSnapshot
  /-- Immutable public and deferred commitment words. -/
  commitments : CommitmentStatement
  /-- Inclusive resource ceilings for this local segment. -/
  limits : ResourceLimits := ResourceLimits.native SP1Prime

/-- Internal interpretation for the existing fixed-clock host proof. -/
def Context.withClock (context : Context) (clock : BitVec 48) : FixedHintAssembly.Context where
  image := context.image
  source := context.source
  target := context.target
  cursorClock := clock
  commitments := context.commitments
  limits := context.limits

/-- The projected host assembly interpreted at the timestamp supplied by the physical terminal. -/
abbrev base (context : Context) (clock : BitVec 48) := FixedHintAssembly.assembly (context.withClock clock)

/-- The canonical verifier endpoint uses the target queue head and the source allocation frontier. -/
def publicCursor (context : Context) : HostHintQueue.State Fp := (context.withClock 0).finalHints

theorem fixed_tables (context : Context) (a b : BitVec 48) : (base context a).tables = (base context b).tables := by
  simp only [base, FixedHintAssembly.tables_eq, FixedHintAssembly.withoutCommitments, Shard.installed, HostObserved.ensemble,
    ClosedVerifier.withInteractions, HostObserved.producers, HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble,
    PublicVerifier.install, HostFinalMemory.tables_eq, Context.withClock]

private theorem sameExtension (name : String) (left right : Ensemble Fp SP1PublicIO) (same : left.channels = right.channels) :
    left.channels ++ [VerifierChannel.channel name left] = right.channels ++ [VerifierChannel.channel name right] := by
  simp only [VerifierChannel.channel, VerifierChannel.channelName, VerifierChannel.channelNames, same]

theorem fixed_channels (context : Context) (a b : BitVec 48) : (base context a).channels = (base context b).channels := by
  repeat' apply sameExtension
  rfl

private theorem fresh (context : Context) :
    (HostHintQueueTerminal.component (publicCursor context)).circuit.name ∉ (base context 0).tables.map (·.circuit.name) := by
  change "sp1.native.hint_queue.terminal" ∉ _
  rw [base, FixedHintAssembly.tables_eq, List.map_append, FixedHintAssembly.withoutCommitments,
    Shard.installed, HostObserved.table_names]
  simp only [HostFinalMemory.Installed, HostFinalMemory.ensemble, ClosedVerifier.install,
    HostFinalMemory.withReceipts, HostFinalMemory.withRegisters, FinalReceiptEnsemble.install,
    Ensemble.replaceComponent, HostFinalMemory.base, HostHintQueueBoundary.ensemble, HaltPadding.install,
    HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
    HostLocalCore.baseEnsemble]
  simp only [List.map_set, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
    LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
    SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
    MemorySnapshot.registerTable, StaticTable.ofRows, FinalMemoryChecks.checkTables,
    FinalRegisterValue.membership, HostHintReadLocal.sourceResources, HostHintReadLocal.bankResources,
    HostHintQueue.source, HostHintQueue.sourceWord, StaticTable.payloadComponent, StaticTable.payloadProvider]
  exact of_decide_eq_true rfl

private theorem registered (context : Context) :
    HostHintQueue.stateChannel.toRaw ∈ (base context 0).channels := by
  change _ ∈ ((((_ ++ [_]) ++ [_]) ++ [_]) ++ [_])
  apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
  apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  simp [HostLocalCore.baseEnsemble, HostLocalCore.registry, HostFinalMemory.sourceChannels]

/-- The final physical slot receives the two authenticated pointers at the private last clock. -/
def assembly (context : Context) : Ensemble Fp SP1PublicIO :=
  let old := base context 0
  let row := HostHintQueueTerminal.component (publicCursor context)
  { old with tables := old.tables ++ [row]
             unique_names := by simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append]
               using old.unique_names.concat (fresh context)
             tables_channels := by
               intro table member channel used
               rcases List.mem_append.mp member with original | terminal
               · exact old.tables_channels table original used
               · obtain rfl := List.mem_singleton.mp terminal
                 change channel ∈ [HostHintQueue.stateChannel.toRaw, HostHintQueue.stateChannel.toRaw] at used
                 rcases List.mem_cons.mp used with rfl | singleton
                 · exact registered context
                 · exact (List.mem_singleton.mp singleton) ▸ registered context }

/-- The physical order keeps the host assembly, then both statement providers. -/
theorem tables_eq (context : Context) : (assembly context).tables =
    (FixedHintAssembly.withoutCommitments (context.withClock 0)).tables ++
      [CommitmentDeclaration.source context.commitments, HostHintQueueTerminal.component (publicCursor context)] := by
  change (base context 0).tables ++ [_] = _
  rw [base, FixedHintAssembly.tables_eq, List.append_assoc]
  rfl

theorem tables_length (context : Context) : (assembly context).tables.length = 100 := by
  change ((base context 0).tables ++ [_]).length = _
  rw [List.length_append, FixedHintAssembly.tables_length]
  rfl

/-- The unique physical slot installed after the fixed-cursor assembly. -/
def terminalSlot (context : Context) : TableSlot (assembly context).tables (HostHintQueueTerminal.component (publicCursor context)) :=
  (TableSlot.ofIndex [HostHintQueueTerminal.component (publicCursor context)] ⟨0, by simp⟩).appendRight (base context 0).tables

/-- Executable verification against the installed component order, channels and public verifier. -/
def description (context : Context) : EnsembleCheck (assembly context) where
  lookups := []
  lookups_unique := .nil
  lookups_complete table member _ used := by
    change table ∈ (base context 0).tables ++ [_] at member
    rcases List.mem_append.mp member with original | terminal
    · rw [FixedHintAssembly.component_lookups (context.withClock 0) table original] at used
      exact False.elim (List.not_mem_nil used)
    · obtain rfl := List.mem_singleton.mp terminal
      simp [HostHintQueueTerminal.component, Component.lookups_eq, Component.rowOperations, HostHintQueueTerminal.circuit,
        HostHintQueueTerminal.main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main,
        Gadgets.Equality.main, circuit_norm] at used

/-- The private input type and its views determine how Clean generates witnesses. -/
def proverAssembly (context : Context) (ProverInput : TypeMap) [ProvableType ProverInput]
    (hints : List HintTable) : Ensemble Fp SP1PublicIO :=
  (assembly context).withProverInput ProverInput hints

/-- An exported assembly accepts exactly the same raw statements as the installed assembly. -/
theorem proverStatement_iff (context : Context) (ProverInput : TypeMap) [ProvableType ProverInput]
    (hints : List HintTable) (header : SP1PublicIO Fp) (heights : List ℕ) :
    (proverAssembly context ProverInput hints).Statement .logUp header heights ↔
      (assembly context).Statement .logUp header heights :=
  Ensemble.withProverInput_statement (assembly context) hints .logUp header heights

end SP1Clean.Export.InstalledAssembly
