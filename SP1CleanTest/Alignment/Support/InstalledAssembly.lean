module

public import SP1Clean.Soundness.HostFinalMemory
public import SP1Clean.Soundness.CommitmentEnsemble
public import ToClean.Air.ChannelRegistry
public import ToClean.Air.TableBuild

/-! # Shared complete installed assembly for export comparisons

Instance data selects the program, source, memory target and host endpoints. Every fixture
uses the same production assembly and physical registry; changing a source from running to
stopped does not replace it with a smaller circuit. This fixture context does not claim the
remaining complete Sail/host target equality or mixed compiler theorem.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

/-- The native SP1 field used by the installed comparison fixtures. -/
abbrev Fp := ZMod SP1Prime

/-- Data determining the complete installed assembly and its verifier. -/
structure Context where
  /-- Committed program and its initial byte image. -/
  image : ProgramImage
  /-- Complete finite incoming Sail, host and clock snapshot. -/
  source : ExecutionSnapshot
  /-- Complete outgoing register and RAM snapshot. -/
  target : MemorySnapshot
  /-- Outgoing authenticated hint-queue cursor. -/
  finalHints : HostHintQueue.State Fp
  /-- Host endpoint supplying the outgoing banks and optional exit status. -/
  finalHost : HostState
  /-- Immutable proof statement, independent of partially populated mutable banks. -/
  commitments : CommitmentStatement

/-- All installed components, source resources and target checks in their canonical order. -/
def withoutCommitments (context : Context) : Ensemble Fp SP1PublicIO :=
  HostFinalMemory.ensemble context.image context.source context.target
    context.finalHints context.finalHost HostCallReceivers.available
    (HostHintReadLocal.sourceResources context.source.host.io.hints) []
    (HostFinalMemory.source_unique_names context.image context.source context.target)

/-- The declaration provider has a fresh name in the complete host inventory. -/
theorem declaration_fresh (context : Context) :
    (CommitmentDeclaration.source (p := SP1Prime) context.commitments).circuit.name ∉
      (withoutCommitments context).tables.map (·.circuit.name) := by
  change "sp1.native.commitment_declaration.source" ∉ _
  simp only [withoutCommitments, HostFinalMemory.ensemble, ClosedVerifier.install,
    HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base,
    HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble,
    HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
    HostLocalCore.baseEnsemble]
  simp only [List.map_set, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
    LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
    SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
    MemorySnapshot.registerTable, StaticTable.ofRows, FinalMemoryChecks.checkTables,
    FinalRegisterValue.membership, HostHintReadLocal.sourceResources,
    HostHintQueue.source, HostHintQueue.sourceWord, StaticTable.payloadComponent,
    StaticTable.payloadProvider]
  exact of_decide_eq_true rfl

/-- Complete production assembly with the verifier-owned commitment statement installed. -/
def assembly (context : Context) : Ensemble Fp SP1PublicIO :=
  CommitmentEnsemble.install context.commitments (withoutCommitments context) (declaration_fresh context)

theorem without_tables_length (context : Context) : (withoutCommitments context).tables.length = 94 := by
  simp only [withoutCommitments, HostFinalMemory.ensemble, ClosedVerifier.install,
    HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.length_set,
    HostFinalMemory.base_tables_length]
  rfl

theorem tables_eq (context : Context) : (assembly context).tables =
    (withoutCommitments context).tables ++ [CommitmentDeclaration.source context.commitments] := rfl

theorem tables_length (context : Context) : (assembly context).tables.length = 95 := by
  rw [tables_eq, List.length_append, without_tables_length]
  rfl

/-- One consumer input at its actual physical table position. -/
structure Seed where
  /-- Position in the complete installed physical inventory. -/
  table : ℕ
  /-- Exact input cells for the selected component. -/
  cells : List Fp

/-- Construct a consumer seed from its physical position and input cells. -/
def Seed.ofCells (table : ℕ) (cells : List Fp) : Seed := ⟨table, cells⟩

/-- Decode only after validating the seed's exact input width. -/
def Seed.input (seed : Seed) (component : Component Fp) : component.Input Fp :=
  fromElements (Vector.ofFn fun index => seed.cells[index.val]?.getD 0)

/-- Finite fixture construction uses the same component interface as native witnesses. -/
def Seed.build (seed : Seed) (component : Component Fp) (data : ProverData Fp) : Array Fp :=
  component.buildRow (seed.input component) data (ProverHint.empty Fp)

/-- No seed may name an absent/fixed table or silently truncate an input row. -/
def seedValid (tables : List (Component Fp)) (seed : Seed) : Bool :=
  match tables[seed.table]? with
  | none => false
  | some component => component.fixedColumns.isNone && seed.cells.length == component.rowOffset

/-- One complete register/RAM message, with canonical address and value limbs. -/
def memoryRecord (address clock : ℕ) (value : BitVec 64) : Channels.MemoryMsg Fp :=
  let key := Address.ofNat (p := SP1Prime) address
  ⟨0, clock, key[0], key[1], key[2], Target.bitVecToWord value⟩

/-- Ordered source/final register records and exact target checks shared by host fixtures. -/
def registerSeeds (context : Context) (registers : List (ℕ × ℕ)) : List Seed :=
  (registers.foldl (fun (acc : ℕ × List Seed) (address, clock) =>
    let index := BitVec.ofNat 5 address
    let record := memoryRecord address clock (context.target.read (.reg index))
    let initial := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate context.source.sail.memorySnapshot index) acc.1 address
    let final := OrderedMemoryProvider.populate record acc.1 address
    let selected : Fp := if Semantics.MemLoc.reg index ∈ context.source.sail.memorySnapshot.changes context.target then 1 else 0
    (address + 1, acc.2 ++ [⟨0, (toElements initial).toList⟩, ⟨3, (toElements final).toList⟩,
      ⟨90, (toElements (M := FinalRegisterCheck.RowInput)
        ((⟨record, selected⟩, 1) : FinalRegisterCheck.RowInput Fp)).toList⟩])) (0, [])).2

/-- An empty segment still closes both ordered inventories, both banks and public Exit.
Positions are resolved from actual component names and validated before generation. -/
def emptyConsumers (context : Context) : List Seed :=
  let tables := (assembly context).tables
  let final := OrderedMemoryEnsemble.endKey (p := SP1Prime)
  let ordered := toElements (OrderedBoundaryEnd.populate (Vector.replicate 4 0) final) |>.toList
  let bank (deferred : Bool) := toElements (HostCommitBoundary.start
    (HostCommitEnsemble.sourceValues (p := SP1Prime) deferred context.source.host)) |>.toList
  [(OrderedBoundaryEnd.circuit (p := SP1Prime) SnapshotMemoryEnsemble.channelName final |>.name, ordered),
   (OrderedBoundaryEnd.circuit (p := SP1Prime) OrderedFinalProvider.channelName final |>.name, ordered),
   ((HostCommitBoundary.terminal (p := SP1Prime) false).name, bank false),
   ((HostCommitBoundary.terminal (p := SP1Prime) true).name, bank true),
   ((HaltPaddingChip.circuit (p := SP1Prime)).name, List.replicate (size HaltChip.Inputs) 0)].map
    fun (name, cells) =>
      ⟨tables.findIdx (fun component => component.circuit.name == name), cells⟩

end SP1CleanTest.Alignment.InstalledAssembly
