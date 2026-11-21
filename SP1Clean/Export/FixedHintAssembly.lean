import SP1Clean.Soundness.Shard.Trace
import SP1Clean.Semantics.ReleasePolicy
import SP1Clean.Semantics.Resources.SixCallResources
import SP1Clean.Native.Operations.HostHintTarget
import SP1Clean.Soundness.Shard.TargetEndpoint
import SP1Clean.Soundness.ResourceEnsemble

/-! # Host assembly at a recovered hint timestamp

The physical public assembly projects to these 99 slots at the timestamp recovered from its
terminal table. This module proves the source-to-target observations of that projection.
-/

namespace SP1Clean.Export.FixedHintAssembly

open Circuit Air.Flat SP1Clean.Semantics SP1Clean.Soundness

/-- The field of the pinned SP1 supervisor assembly. -/
abbrev Fp := ZMod SP1Prime

/-- Data determining the complete installed assembly and its verifier. -/
structure Context where
  /-- Committed program and its initial byte image. -/
  image : ProgramImage
  /-- Complete finite incoming Sail, host and clock snapshot. -/
  source : ExecutionSnapshot
  /-- Complete outgoing snapshot supplying the register, RAM, host bank and exit endpoints. -/
  target : ExecutionSnapshot
  /-- Timestamp of the last HINT_LEN or HINT_READ, or zero when neither occurred. -/
  cursorClock : BitVec 48
  /-- Immutable proof statement, independent of partially populated mutable banks. -/
  commitments : CommitmentStatement
  /-- Inclusive numeric bounds of the local segment. -/
  limits : ResourceLimits := ResourceLimits.native SP1Prime

/-- Each suffix of the immutable source queue has a head equal to its remaining length.
The allocation frontier stays at the size of the incoming queue throughout the six-call profile. -/
def Context.finalHints (context : Context) : HostHintQueue.State Fp :=
  HostHintQueue.State.encode context.cursorClock.toNat context.target.host.io.hints.length
    context.source.host.io.hints.length

/-- All installed components, source resources and target checks in their canonical order. -/
abbrev withoutCommitments (context : Context) : Ensemble Fp SP1PublicIO :=
  Shard.installed context.image context.source context.target context.finalHints

/-- The declaration provider has a fresh name in the complete host inventory. -/
private theorem declarationFresh (context : Context) :
    (CommitmentDeclaration.source (p := SP1Prime) context.commitments).circuit.name ∉
      (withoutCommitments context).tables.map (·.circuit.name) := by
  change "sp1.native.commitment_declaration.source" ∉ _
  rw [withoutCommitments, Shard.installed, HostObserved.table_names]
  simp only [HostFinalMemory.Installed,
    HostFinalMemory.ensemble, ClosedVerifier.install, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base,
    HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble,
    HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
    HostLocalCore.baseEnsemble]
  simp only [List.map_set, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
    LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
    SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
    MemorySnapshot.registerTable, StaticTable.ofRows, FinalMemoryChecks.checkTables,
    FinalRegisterValue.membership, HostHintReadLocal.sourceResources, HostHintReadLocal.bankResources,
    HostHintQueue.source, HostHintQueue.sourceWord, StaticTable.payloadComponent,
    StaticTable.payloadProvider]
  exact of_decide_eq_true rfl

/-- The six-call assembly with its verifier-owned commitment statement. -/
def committedAssembly (context : Context) : Ensemble Fp SP1PublicIO :=
  CommitmentEnsemble.install context.commitments (withoutCommitments context) (declarationFresh context)
    (Shard.declarationsRegistered context.image context.source context.target context.finalHints)

/-- Check the invariant Sail frame, canonical public endpoints, and exact outgoing host. -/
def assembly (context : Context) : Ensemble Fp SP1PublicIO :=
  ResourceEnsemble.install context.limits context.source context.target
    ((HostHintTarget.checker context.source.host context.target.host (Address.toNat context.finalHints.head)).install
      (committedAssembly context))

/-- Facts enforced by the static and public boundary circuits of the exported assembly. -/
structure TargetChecks (context : Context) (header : SP1PublicIO Fp) : Prop where
  /-- Exact ordered hint suffix and preserved host streams. -/
  host : HostHintTarget.Spec context.source.host context.target.host (Address.toNat context.finalHints.head)
  /-- Inclusive boundary occupancy and elapsed ticks. -/
  resources : ResourceBoundary.Spec context.limits context.source context.target header

/-- Boundary installation preserves the height vector and adds the checked contracts. -/
theorem boundary_statement_iff (context : Context) (header : SP1PublicIO Fp) (heights : List ℕ) :
    (assembly context).Statement .logUp header heights ↔
      (committedAssembly context).Statement .logUp header heights ∧ TargetChecks context header := by
  let head := Address.toNat context.finalHints.head
  rw [assembly, ResourceEnsemble.statement_iff,
    (HostHintTarget.checker context.source.host context.target.host head).statement_iff _
    (HostHintTarget.count_bound ..) (fun _ => HostHintTarget.Spec context.source.host context.target.host head)
    (HostHintTarget.checks_iff context.source.host context.target.host head)]
  exact ⟨fun ⟨⟨accepted, host⟩, resources⟩ => ⟨accepted, host, resources⟩,
    fun ⟨accepted, host, resources⟩ => ⟨⟨accepted, host⟩, resources⟩⟩

private theorem baseTableCount (context : Context) : (withoutCommitments context).tables.length = 98 := by
  have names := HostObserved.table_names (image := context.image) (source := context.source)
    (target := context.target) (final := context.finalHints)
  have counts := congrArg List.length names
  simp only [List.length_map] at counts
  rw [withoutCommitments, Shard.installed, counts]
  simp only [HostFinalMemory.Installed,
    HostFinalMemory.ensemble, ClosedVerifier.install, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.length_set,
    HostFinalMemory.base_tables_length]
  rfl

/-- Installing the commitment statement appends its single verifier-fixed provider. -/
theorem tables_eq (context : Context) : (assembly context).tables =
    (withoutCommitments context).tables ++ [CommitmentDeclaration.source context.commitments] := rfl

/-- Number of physical components in the installed supervisor assembly. -/
theorem tables_length (context : Context) : (assembly context).tables.length = 99 := by
  rw [tables_eq, List.length_append, baseTableCount]
  rfl

/-- Every installed component is lookup-free, including currently unused physical slots. -/
theorem component_lookups (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) : component.operations.lookups = [] := by
  rw [tables_eq] at member
  rcases List.mem_append.mp member with original | added
  · exact HostObserved.lookupFree component original
  · obtain rfl := List.mem_singleton.mp added
    simp [CommitmentDeclaration.source, StaticTable.payloadComponent, StaticTable.payloadProvider,
      Component.lookups_eq, Component.rowOperations, circuit_norm]

/-- Each raw public statement of the production assembly gives a machine trace from the source. -/
theorem trace_of_statement (context : Context)
    {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    Shard.SailTrace context.commitments context.image context.source context.target context.finalHints
      header ∧ TargetChecks context header := by
  obtain ⟨committed, boundaries⟩ := (boundary_statement_iff context header heights).mp accepted
  exact ⟨Shard.sail_trace committed, boundaries⟩

end SP1Clean.Export.FixedHintAssembly
