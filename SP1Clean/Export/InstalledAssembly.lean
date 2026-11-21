import SP1Clean.Export.InstalledHintProjection
import SP1Clean.Export.InstalledHintVerifier
import ToClean.Air.MessageFilter

/-! # Soundness with a private queue timestamp -/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Soundness Semantics
open HostHintQueue (stateChannel)
open scoped Classical

private abbrev Ledger := List (Interaction Fp)

/-- Adding the terminal and the verifier pull preserves each signed cursor balance. -/
theorem cancel_terminal (first last : Ledger) (publicCursor privateCursor : HostHintQueue.State Fp) :
    LogUpBalanced (first ++ [stateChannel.pulledValue publicCursor] ++ last ++
      [stateChannel.pulledValue privateCursor, stateChannel.pushedValue publicCursor]) ↔
    LogUpBalanced (first ++ [stateChannel.pulledValue privateCursor] ++ last) := by
  apply forall_congr'
  intro message
  simp only [balanceOf_append, balanceOf_cons, Channel.pulledValue, Channel.pushedValue, Interaction.signedMult]
  have empty : balanceOf ([] : Ledger) message = 0 := rfl
  rw [empty]
  split_ifs <;> ring_nf

private theorem project_heights {context : Context} (witness : EnsembleWitness (assembly context)) (clock : BitVec 48) :
    (project witness clock).heights = witness.heights.take 99 := by
  simp only [EnsembleWitness.heights, project, EnsembleWitness.ofTables_tables, ← List.map_take]
  change List.map (fun t : Table Fp => t.table.length) (withDerivedData _ _ _) = _
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map List.length) (withDerivedData_map_table (witness.tables.take 99) _ (toElements witness.publicInput).toArray)

attribute [local irreducible] assembly FixedHintAssembly.assembly

private theorem split_ledgers {context : Context} (witness : EnsembleWitness (assembly context)) (clock : BitVec 48)
    (channel : RawChannel Fp)
    (physical : ((terminalSlot context).table witness).interactionsWith stateChannel.toRaw =
      [stateChannel.pulledValue (context.withClock clock).finalHints, stateChannel.pushedValue (publicCursor context)]) :
    ∃ first last : Ledger,
      (project witness clock).interactionsWith channel =
        first ++ (if channel = stateChannel.toRaw then [stateChannel.pulledValue (context.withClock clock).finalHints] else []) ++ last ∧
      witness.interactionsWith channel =
        first ++ (if channel = stateChannel.toRaw then [stateChannel.pulledValue (publicCursor context)] else []) ++ last ++
          (if channel = stateChannel.toRaw then [stateChannel.pulledValue (context.withClock clock).finalHints,
            stateChannel.pushedValue (publicCursor context)] else []) := by
  let old := project witness clock
  let env := witness.data.publicEnvironment
  obtain ⟨first, last, vary⟩ := verifier_split context env channel
  have oldVerifier : old.verifierInteractionsWith channel =
      (base context clock).verifierOperations.interactionValuesWith channel env :=
    Operations.interactionValuesWith_congr rfl
  have newVerifier : witness.verifierInteractionsWith channel =
      (base context 0).verifierOperations.interactionValuesWith channel env := by
    unfold EnsembleWitness.verifierInteractionsWith assembly
    rfl
  have tableLedger := project_tables_ledger witness clock channel
  refine ⟨first, last ++ old.tables.flatMap (·.interactionsWith channel), ?_, ?_⟩
  · change old.verifierInteractionsWith channel ++ old.tables.flatMap _ = _
    rw [oldVerifier, vary clock, List.append_assoc]
  · change witness.verifierInteractionsWith channel ++ witness.tables.flatMap _ = _
    rw [newVerifier, vary 0, ← tableLedger]
    by_cases same : channel = stateChannel.toRaw
    · subst channel
      rw [physical]
      simp only [ite_true, publicCursor, List.append_assoc, old]
    · simp only [ite_eq_right same, terminal_silent witness same, List.append_nil, List.append_assoc, old]

/-- Every accepted physical witness projects to the old checked assembly at the timestamp of the
actual terminal row. The retained table heights are the literal public prefix. -/
theorem project_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ clock : BitVec 48, (base context clock).Statement .logUp header (heights.take 99) := by
  obtain ⟨fit, witness, publicEq, heightEq, checked, balance⟩ := accepted
  rw [← heightEq] at fit
  have fits := (witness.interactionsFit_iff .logUp).mp fit
  obtain ⟨clock, physical⟩ := private_clock witness checked
  let old := project witness clock
  have height : old.heights = heights.take 99 := (project_heights witness clock).trans (congrArg (List.take 99) heightEq)
  have raw (channel : RawChannel Fp) (registered : channel ∈ (base context clock).channels) :
      (old.interactionsWith channel).length < ringChar Fp ∧ LogUpBalanced (old.interactionsWith channel) := by
    have present : channel ∈ (assembly context).channels := by
      unfold assembly
      change channel ∈ (base context 0).channels
      rw [fixed_channels context 0 clock]
      exact registered
    obtain ⟨first, last, earlier, actual⟩ := split_ledgers witness clock channel physical
    have enough := fits channel present
    simp only [Balance.logUp, ComputableRingChar.char_eq, decide_eq_true_eq] at enough
    have funded := balance channel present
    change LogUpBalanced (witness.interactionsWith channel) at funded
    rw [actual] at enough funded
    change ((project witness clock).interactionsWith channel).length < ringChar Fp ∧
      LogUpBalanced ((project witness clock).interactionsWith channel)
    rw [earlier]
    by_cases same : channel = stateChannel.toRaw
    · simp only [ite_eq_left same, List.length_append, List.length_cons, List.length_nil] at enough ⊢
      exact ⟨by omega, (cancel_terminal ..).mp (by simpa only [ite_eq_left same] using funded)⟩
    · simpa only [ite_eq_right same, List.append_nil] using And.intro enough funded
  refine ⟨clock, ?_, old, (project_header witness clock).trans publicEq, height, project_constraints witness clock checked,
    fun channel member => (raw channel member).2⟩
  rw [← height, old.interactionsFit_iff]
  exact fun channel member => by simpa only [Balance.logUp, ComputableRingChar.char_eq, decide_eq_true_eq] using (raw channel member).1

/-- Host and resource checks derived from the public snapshots. -/
structure TargetChecks (context : Context) (header : SP1PublicIO Fp) : Prop where
  /-- The target host contains the authenticated suffix and preserved streams. -/
  host : HostHintTarget.Spec context.source.host context.target.host (Address.toNat (publicCursor context).head)
  /-- Public clocks and resource ceilings hold at both boundaries. -/
  resources : ResourceBoundary.Spec context.limits context.source context.target header

/-- The accepted trace observes the two public hint pointers independently of the terminal clock. -/
theorem trace_of_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    Shard.SailTrace context.commitments context.image context.source context.target (publicCursor context)
      header ∧ TargetChecks context header := by
  obtain ⟨clock, projected⟩ := project_statement context accepted
  obtain ⟨⟨valid, sourceFor, sail, declared, events, actual, path, agrees, handlers, links, dynamic, endpoint⟩, checks⟩ :=
    FixedHintAssembly.trace_of_statement (context.withClock clock) projected
  refine ⟨⟨valid, sourceFor, sail, declared, events, actual, path, agrees, handlers, links, dynamic, ?_⟩,
    ⟨checks.host, checks.resources⟩⟩
  exact ⟨endpoint.clock, endpoint.pc, endpoint.nextPC, endpoint.increment, endpoint.retired, endpoint.interrupts,
    endpoint.eventIndex, endpoint.preserved, endpoint.runtime, endpoint.registers, endpoint.ram, endpoint.host, endpoint.exit⟩

/-- Public observations of the six-handler execution between both complete snapshots, including
the released jump-link check at every replayed ordinary source. -/
structure ExecutionFacts (context : Context) (header : SP1PublicIO Fp)
    (events : List Machine.ExecutionEvent) : Prop where
  path : (FormalModel.Shard.sp1Machine SP1Prime context.image).Trace context.source.realize events context.target.realize
  endpoint : Shard.Endpoint context.source context.target (publicCursor context) header events context.target.realize
  handlers : ∀ event ∈ events, SixCallProfile.event event
  commitments : context.commitments.Matches events
  releaseLinks : ExecutionPath.ReleaseLinks (FormalModel.Shard.policy SP1Prime context.image)
    context.image.program context.source.realize events
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
  obtain ⟨⟨valid, sourceFor, sail, declared, events, actual, path, agrees, handlers, links, dynamic, endpoint⟩, checked⟩ :=
    trace_of_statement context accepted
  obtain rfl := (endpoint.realize_eq sail dynamic checked.host).symm
  have execution := FormalModel.Shard.trace_iff_executionPath.mp path
  obtain ⟨clock, ticks, count⟩ := checked.resources.path_work execution endpoint.clock
  refine ⟨valid, sourceFor, sail, declared, events,
    ⟨path, endpoint, handlers, agrees, links, ticks, count, checked.resources, ?_⟩⟩
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
