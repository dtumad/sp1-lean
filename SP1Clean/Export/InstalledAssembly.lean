import SP1Clean.Soundness.Shard.Trace
import SP1Clean.Semantics.ReleasePolicy
import SP1Clean.Semantics.Resources.SixCallResources
import SP1Clean.Native.Operations.HostHintTarget
import SP1Clean.Soundness.Shard.TargetEndpoint
import SP1Clean.Soundness.ResourceEnsemble
import ToClean.Air.EnsembleCheck
import ToClean.Air.ProverInputStatement

/-! # The installed SP1 supervisor assembly

Program and complete source and target snapshots, a hint endpoint and an immutable commitment
statement select the assembly. Its verifier, physical tables and channel registry are shared by
the public statement, finite witness checker and Clean's witness-generation interface.
-/

namespace SP1Clean.Export.InstalledAssembly

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
  lastHintClock : BitVec 48
  /-- Immutable proof statement, independent of partially populated mutable banks. -/
  commitments : CommitmentStatement
  /-- Inclusive numeric bounds of the local segment. -/
  limits : ResourceLimits := ResourceLimits.native SP1Prime

/-- Each suffix of the immutable source queue has a head equal to its remaining length.
The allocation frontier stays at the size of the incoming queue throughout the six-call profile. -/
def Context.finalHints (context : Context) : HostHintQueue.State Fp :=
  HostHintQueue.State.encode context.lastHintClock.toNat context.target.host.io.hints.length
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

/-- Check physical rows, occurrence capacity and balance against the installed verifier. -/
def description (context : Context) : EnsembleCheck (assembly context) where
  lookups := []
  lookups_unique := .nil
  lookups_complete component member _ used := by
    rw [component_lookups context component member] at used
    exact False.elim (List.not_mem_nil used)

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

/-- Each raw public statement of the production assembly gives a machine trace from the source. -/
theorem trace_of_statement (context : Context)
    {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    Shard.SailTrace context.commitments context.image context.source context.target context.finalHints
      header ∧ TargetChecks context header := by
  obtain ⟨committed, boundaries⟩ := (boundary_statement_iff context header heights).mp accepted
  exact ⟨Shard.sail_trace committed, boundaries⟩

/-- Public observations of the six-handler execution between both complete snapshots. -/
structure ExecutionFacts (context : Context) (header : SP1PublicIO Fp)
    (events : List Machine.ExecutionEvent) : Prop where
  path : (FormalModel.Shard.sp1Machine SP1Prime context.image).Trace context.source.realize events context.target.realize
  endpoint : Shard.Endpoint context.source context.target context.finalHints header events context.target.realize
  handlers : ∀ event ∈ events, SixCallProfile.event event
  commitments : context.commitments.Matches events
  ticks : executionResources (FormalModel.Shard.policy SP1Prime context.image) context.image.program
    context.source.realize events .ticks ≤ context.limits.ticks
  count : 8 * events.length ≤ context.target.clock - context.source.clock
  resources : ResourceBoundary.Spec context.limits context.source context.target header
  empty : header.is_execution_shard = 0 ↔ events = []

/-- Raw acceptance gives a bounded execution from the authenticated source. All outgoing host,
clock, memory, public commitment and handler observations refer to that execution. -/
theorem execution_of_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    ExecutionSourceValid context.image context.source ∧ header.SourceFor context.source ∧
      SailBoundary.Spec context.source context.target header ∧ CommitmentBoundary.Spec context.commitments header ∧
      ∃ events, ExecutionFacts context header events := by
  obtain ⟨⟨valid, sourceFor, sail, declared, events, actual, path, agrees, handlers, dynamic, endpoint⟩, checked⟩ :=
    trace_of_statement context accepted
  obtain rfl := (endpoint.realize_eq sail dynamic checked.host).symm
  have execution := FormalModel.Shard.trace_iff_executionPath.mp path
  obtain ⟨clock, ticks, count⟩ := checked.resources.path_work execution endpoint.clock
  refine ⟨valid, sourceFor, sail, declared, events,
    ⟨path, endpoint, handlers, agrees, ticks, count, checked.resources, ?_⟩⟩
  rw [sail.2.2]
  by_cases same : context.source.clock = context.target.clock
  · have noEvents : events.length = 0 := by omega
    simp only [SailBoundary.executionShardFlag, ite_eq_left same, List.length_eq_zero_iff.mp noEvents]
  · simp only [SailBoundary.executionShardFlag, ite_eq_right same, one_ne_zero, false_iff]
    rintro rfl
    have identity := ExecutionPath.nil_iff.mp execution
    exact same ((congrArg ExecutionState.clock identity).symm.trans clock)


/-- Raw acceptance of the exported assembly implies a six-handler SP1 trace between the
complete supplied Sail, host and clock states, with one immutable commitment statement. -/
theorem soundness (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ events : List Machine.ExecutionEvent, (FormalModel.Shard.sp1Machine SP1Prime context.image).Trace context.source.realize events context.target.realize ∧
      context.commitments.Matches events ∧ ∀ event ∈ events, SixCallProfile.event event := by
  obtain ⟨trace, checked⟩ := trace_of_statement context accepted
  exact trace.realized checked.host

/-- On an accepted shard the execution flag is zero exactly when the empty tape satisfies
all clauses of the full resource-bounded statement between the supplied boundaries. -/
theorem executionFlag_iff_identity (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    header.is_execution_shard = 0 ↔
      FormalModel.Shard.StatementExecution context.limits SP1Prime context.commitments context.image context.source context.target [] := by
  obtain ⟨valid, _, _, fixed, events, facts⟩ := execution_of_statement context accepted
  constructor
  · intro flag
    obtain rfl := facts.empty.mp flag
    obtain ⟨incoming, outgoing, _, _, time, pc⟩ := facts.resources.1
    rw [← context.source.resources_realize] at incoming
    rw [← context.target.resources_realize] at outgoing
    exact ⟨⟨⟨valid, FormalModel.Shard.trace_iff_executionPath.mp facts.path⟩,
      ExecutionPath.encoded_nil, ResourceUsage.zero_fits _, incoming, outgoing, time, pc⟩,
      fixed.1, facts.commitments⟩
  · intro empty
    have same := ExecutionPath.nil_iff.mp empty.1.1.2
    have clock : context.target.clock = context.source.clock := congrArg ExecutionState.clock same
    have bound := facts.count
    rw [clock, Nat.sub_self] at bound
    exact facts.empty.mpr (List.length_eq_zero_iff.mp (by omega))

/-- Every cut of the recovered execution respects the declared hint, request and output
ceilings, including the intermediate state and the peak so far. -/
theorem ExecutionFacts.prefix_host_bounds {context : Context} {header : SP1PublicIO Fp}
    {events : List Machine.ExecutionEvent} (facts : ExecutionFacts context header events)
    (cut : ℕ) :
    let policy := FormalModel.Shard.policy SP1Prime context.image
    ∃ middle, ExecutionPath policy context.image.program context.source.realize (events.take cut) middle ∧
      ExecutionPath policy context.image.program middle (events.drop cut) context.target.realize ∧
      ∀ kind ∈ [ResourceKind.liveHints, .liveHintBytes, .requests, .outputBytes],
        executionResources policy context.image.program context.source.realize (events.take cut) kind ≤
          context.limits.ceiling kind ∧ middle.resources kind ≤ context.limits.ceiling kind := by
  obtain ⟨middle, left, right, bounds⟩ := SixCallProfile.prefix_host_bounds
    (FormalModel.Shard.trace_iff_executionPath.mp facts.path) facts.handlers cut
  refine ⟨middle, left, right, fun kind member => ?_⟩
  have ceiling := facts.resources.1.1 kind
  rw [← context.source.resources_realize] at ceiling
  exact ⟨(bounds kind member).1.trans ceiling, (bounds kind member).2.trans ceiling⟩

/-- A segment beginning in a stopped host is the complete identity on its actual source. -/
theorem ExecutionFacts.of_stopped {context : Context} {header : SP1PublicIO Fp}
    {events : List Machine.ExecutionEvent}
    (facts : ExecutionFacts context header events) (stopped : context.source.host.exitCode ≠ none) :
    events = [] ∧ context.target.realize = context.source.realize :=
  (FormalModel.Shard.trace_iff_executionPath.mp facts.path).of_halted stopped

/-- For a running-to-stopped segment, an actual final HALT supplies the public exit code.
The released default exit policy can then be checked on its public field. -/
theorem ExecutionFacts.halted {context : Context} {header : SP1PublicIO Fp}
    {events : List Machine.ExecutionEvent} {code : BitVec 32}
    (facts : ExecutionFacts context header events) (running : context.source.host.exitCode = none)
    (stopped : context.target.host.exitCode = some code) :
    (∃ beforeEvents call, events = beforeEvents ++ [.syscall call] ∧ call.rawCode = 0 ∧ call.arg1.setWidth 32 = code) ∧
      code.toNat = header.exit_code.val ∧ (ReleasePolicy.acceptsExit code = true ↔ header.exit_code = 0) := by
  obtain ⟨beforeEvents, _, call, last, _, _, halt, operand⟩ :=
    (FormalModel.Shard.trace_iff_executionPath.mp facts.path).ends_in_halt running stopped
  have exitCode := facts.endpoint.exit code running stopped
  refine ⟨⟨beforeEvents, call, last, halt, operand⟩, exitCode, ?_⟩
  rw [ReleasePolicy.acceptsExit_iff, ← BitVec.toNat_inj, ← ZMod.val_eq_zero, ← exitCode]
  rfl

end SP1Clean.Export.InstalledAssembly
