import SP1Clean.Export.InstalledHintAssembly

/-! # The single public queue pull in the timestamp-indexed verifier -/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Soundness Semantics
open scoped Classical

private abbrev Ledger := List (Interaction Fp)

private noncomputable def pull (context : Context) (channel : RawChannel Fp) (clock : BitVec 48) : Ledger :=
  if channel = HostHintQueue.stateChannel.toRaw then
    [HostHintQueue.stateChannel.pulledValue (context.withClock clock).finalHints] else []

private def Varies (context : Context) (channel : RawChannel Fp) (ledger : BitVec 48 → Ledger) : Prop :=
  ∃ first last, ∀ clock, ledger clock = first ++ pull context channel clock ++ last

private theorem appendFixed {context : Context} {channel : RawChannel Fp} {left right : BitVec 48 → Ledger}
    (varies : Varies context channel left) (fixed : ∀ clock, right clock = right 0) :
    Varies context channel (fun clock => left clock ++ right clock) := by
  obtain ⟨first, last, formula⟩ := varies
  exact ⟨first, last ++ right 0, fun clock => by dsimp only; rw [formula, fixed clock, List.append_assoc]⟩

private theorem prependFixed {context : Context} {channel : RawChannel Fp} {left right : BitVec 48 → Ledger}
    (fixed : ∀ clock, left clock = left 0) (varies : Varies context channel right) :
    Varies context channel (fun clock => left clock ++ right clock) := by
  obtain ⟨first, last, formula⟩ := varies
  exact ⟨left 0 ++ first, last, fun clock => by dsimp only; rw [formula, fixed clock]; simp only [List.append_assoc]⟩

private theorem queue (context : Context) (env : Environment Fp) (channel : RawChannel Fp) :
    Varies context channel (fun clock =>
      ((SP1Clean.HostHintQueueBoundary.main context.source.host.io.hints (context.withClock clock).finalHints ()).operations 0).interactionValuesWith channel env) := by
  by_cases same : channel = HostHintQueue.stateChannel.toRaw
  · subst channel
    refine ⟨[HostHintQueue.stateChannel.pushedValue (SP1Clean.HostHintQueueBoundary.initial context.source.host.io.hints)], [], fun clock => ?_⟩
    simp [SP1Clean.HostHintQueueBoundary.values, pull]
  · refine ⟨[], [], fun clock => ?_⟩
    simp [Operations.interactionValuesWith, Operations.interactionsWith, SP1Clean.HostHintQueueBoundary.main,
      ChannelInteraction.toRaw, circuit_norm, Ne.symm same, pull, same]

private abbrev host (context : Context) (clock : BitVec 48) :=
  Soundness.HostHintQueueBoundary.boundary context.source (context.withClock clock).finalHints context.target.host

private theorem hostEmission (context : Context) (env : Environment Fp) (channel : RawChannel Fp) :
    Varies context channel (fun clock => (host context clock).emit.circuitOperations.interactionValuesWith channel env) := by
  simp only [ClosedVerifier.emit_values, ClosedVerifier.operations, host, Soundness.HostHintQueueBoundary.boundary,
    HostBoundary.closed_main, HostBoundary.values]
  apply appendFixed _ (fun _ => rfl)
  apply appendFixed _ (fun _ => rfl)
  apply appendFixed _ (fun _ => rfl)
  exact queue context _ channel

private theorem closedValues (closed : ClosedVerifier Fp) (before : Ensemble Fp SP1PublicIO)
    (env : Environment Fp) (channel : RawChannel Fp) :
    (closed.program before).circuitOperations.interactionValuesWith channel env =
      closed.emit.circuitOperations.interactionValuesWith channel env ++
        (Verifier.checkZeros (closed.channelName before) closed.operations.constraints).circuitOperations.interactionValuesWith channel env := by
  change ((closed.emit >>= fun _ => Verifier.checkZeros (closed.channelName before) closed.operations.constraints).circuitOperations.interactionValuesWith channel env) = _
  simp only [VerifierM.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.interactionValuesWith, Operations.interactionsWith,
    Operations.interactions_append, List.filter_append, List.map_append]

private theorem hostConstraints (context : Context) (clock : BitVec 48) :
    (host context clock).operations.constraints = (host context 0).operations.constraints := by
  simp only [host, Soundness.HostHintQueueBoundary.boundary, ClosedVerifier.operations, HostBoundary.closed_main,
    HostBoundary.main, circuit_norm, SP1Clean.HostHintQueueBoundary.circuit, SP1Clean.HostHintQueueBoundary.main,
    HostCommitEndpoint.circuit, HostCommitEndpoint.main, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain,
    HostExitBoundary.circuit, HostExitBoundary.main]

private theorem hostProgram (context : Context) (before : Ensemble Fp SP1PublicIO) (env : Environment Fp) (channel : RawChannel Fp) :
    Varies context channel (fun clock => ((host context clock).program before).circuitOperations.interactionValuesWith channel env) := by
  simp only [closedValues]
  apply appendFixed (hostEmission context env channel)
  intro clock
  rw [hostConstraints context clock]
  rfl

private structure Tracks (context : Context) (ensembles : BitVec 48 → Ensemble Fp SP1PublicIO) : Prop where
  registry : ∀ clock, (ensembles clock).channels = (ensembles 0).channels
  ledger : ∀ env channel, Varies context channel (fun clock => (ensembles clock).verifierOperations.interactionValuesWith channel env)

private theorem channelNameEq (stem : String) {left right : Ensemble Fp SP1PublicIO} (same : left.channels = right.channels) :
    VerifierChannel.channelName stem left = VerifierChannel.channelName stem right := by
  simp only [VerifierChannel.channelName, VerifierChannel.channelNames, same]

private theorem Tracks.publicCheck {context : Context} {ensembles : BitVec 48 → Ensemble Fp SP1PublicIO}
    (prior : Tracks context ensembles) (check : PublicVerifier Fp SP1PublicIO) :
    Tracks context (fun clock => check.install (ensembles clock)) where
  registry clock := by
    change (ensembles clock).channels ++ [VerifierChannel.channel check.name (ensembles clock)] =
      (ensembles 0).channels ++ [VerifierChannel.channel check.name (ensembles 0)]
    simp only [VerifierChannel.channel, channelNameEq check.name (prior.registry clock), prior.registry clock]
  ledger env channel := by
    change Varies context channel (fun clock => ((ensembles clock).verifier.andThen
      (check.program (ensembles clock))).circuitOperations.interactionValuesWith channel env)
    simp only [Verifier.Program.andThen_values]
    apply appendFixed (prior.ledger env channel)
    intro clock
    change (Verifier.checkZeros (VerifierChannel.channelName check.name (ensembles clock)) _).circuitOperations.interactionValuesWith channel env =
      (Verifier.checkZeros (VerifierChannel.channelName check.name (ensembles 0)) _).circuitOperations.interactionValuesWith channel env
    rw [channelNameEq _ (prior.registry clock)]

private theorem Tracks.closedCheck {context : Context} {ensembles : BitVec 48 → Ensemble Fp SP1PublicIO}
    (prior : Tracks context ensembles) (check : ClosedVerifier Fp) (registered : ∀ clock, check.circuit.channels ⊆ (ensembles clock).channels) :
    Tracks context (fun clock => check.install (ensembles clock) (registered clock)) where
  registry clock := by
    change (ensembles clock).channels ++ [VerifierChannel.channel check.name (ensembles clock)] =
      (ensembles 0).channels ++ [VerifierChannel.channel check.name (ensembles 0)]
    simp only [VerifierChannel.channel, channelNameEq check.name (prior.registry clock), prior.registry clock]
  ledger env channel := by
    change Varies context channel (fun clock => ((ensembles clock).verifier.andThen
      (check.program (ensembles clock))).circuitOperations.interactionValuesWith channel env)
    simp only [Verifier.Program.andThen_values, closedValues]
    apply appendFixed (prior.ledger env channel)
    intro clock
    simp only [ClosedVerifier.channelName, channelNameEq check.name (prior.registry clock)]

private theorem Tracks.sameVerifier {context : Context} {ensembles changed : BitVec 48 → Ensemble Fp SP1PublicIO}
    (prior : Tracks context ensembles) (registry : ∀ clock, (changed clock).channels = (ensembles clock).channels)
    (program : ∀ clock, (changed clock).verifier = (ensembles clock).verifier) : Tracks context changed where
  registry clock := (registry clock).trans ((prior.registry clock).trans (registry 0).symm)
  ledger env channel := by simpa only [Ensemble.verifierOperations, program] using prior.ledger env channel

private theorem Tracks.interactions {context : Context} {ensembles : BitVec 48 → Ensemble Fp SP1PublicIO}
    (prior : Tracks context ensembles) (check : ClosedVerifier Fp) (registered : ∀ clock, check.circuit.channels ⊆ (ensembles clock).channels) :
    Tracks context (fun clock => check.withInteractions (ensembles clock) (registered clock)) where
  registry := prior.registry
  ledger env channel := by
    change Varies context channel (fun clock => ((ensembles clock).verifier.andThen
      check.interactionProgram).circuitOperations.interactionValuesWith channel env)
    simp only [Verifier.Program.andThen_values]
    exact appendFixed (prior.ledger env channel) (fun _ => rfl)

private abbrev queueBase (context : Context) :=
  let target := context.target.sail.memorySnapshot
  let registration := HostFinalMemory.source_registration (p := SP1Prime) context.image context.source target
  HostHintReadLocal.ensemble context.image context.source HostCallReceivers.available
    (HostHintReadLocal.sourceResources context.source.host.io.hints ++ FinalMemoryChecks.checkTables target)
    (HostFinalMemory.sourceChannels target) (HostFinalMemory.source_unique_names context.image context.source target)
    registration.unique registration.tables

private abbrev beforeMemory (context : Context) (clock : BitVec 48) :=
  let target := context.target.sail.memorySnapshot
  HostFinalMemory.withReceipts context.image context.source target (context.withClock clock).finalHints context.target.host
    HostCallReceivers.available (HostHintReadLocal.sourceResources context.source.host.io.hints)
    (HostFinalMemory.sourceChannels target) (HostFinalMemory.source_unique_names context.image context.source target)
    (HostFinalMemory.source_registration context.image context.source target)

private theorem queueTracks (context : Context) : Tracks context (beforeMemory context) := by
  constructor
  · intro clock
    change (queueBase context).channels ++ [VerifierChannel.channel "host-boundary" (queueBase context)] = _
    rfl
  · intro env channel
    change Varies context channel (fun clock => ((queueBase context).verifier.andThen
      ((host context clock).program (queueBase context))).circuitOperations.interactionValuesWith channel env)
    simp only [Verifier.Program.andThen_values]
    exact prependFixed (fun _ => rfl) (hostProgram context (queueBase context) env channel)

private theorem memoryTracks (context : Context) : Tracks context (fun clock => HostFinalMemory.Installed
    context.image context.source context.target (context.withClock clock).finalHints) :=
  (queueTracks context).closedCheck (FinalMemoryChangeBoundary.closed context.source.sail.memorySnapshot context.target.sail.memorySnapshot) _

private theorem producerTracks (context : Context) : Tracks context (fun clock => HostObserved.producers
    context.image context.source context.target (context.withClock clock).finalHints) :=
  ((memoryTracks context).publicCheck (SailBoundary.checker context.source context.target)).sameVerifier (fun _ => rfl) (fun _ => rfl)

private theorem observationTracks (context : Context) : Tracks context (fun clock => HostObserved.ensemble
    context.image context.source context.target (context.withClock clock).finalHints) :=
  (producerTracks context).interactions (SP1Clean.OrdinaryObservation.endpoint (SP1Clean.OrdinaryObservation.startFor context.source.sail)
    (SP1Clean.OrdinaryObservation.finalFor context.source.sail context.target.sail)) _

private theorem providerFresh (context : FixedHintAssembly.Context) :
    (CommitmentDeclaration.source (p := SP1Prime) context.commitments).circuit.name ∉
      (FixedHintAssembly.withoutCommitments context).tables.map (·.circuit.name) := by
  have unique := (FixedHintAssembly.assembly context).unique_names
  rw [FixedHintAssembly.tables_eq, List.map_append, List.map_cons, List.map_nil, List.nodup_append] at unique
  exact fun member => unique.2.2 _ member _ (List.mem_singleton_self _) rfl

private abbrev provider (context : Context) (clock : BitVec 48) :=
  CommitmentEnsemble.withSource context.commitments (FixedHintAssembly.withoutCommitments (context.withClock clock))
    (providerFresh (context.withClock clock))
    (Shard.declarationsRegistered context.image context.source context.target (context.withClock clock).finalHints)

private theorem providerTracks (context : Context) : Tracks context (provider context) :=
  (observationTracks context).sameVerifier (fun _ => rfl) (fun _ => rfl)

private theorem declarationTracks (context : Context) : Tracks context (fun clock => FixedHintAssembly.committedAssembly (context.withClock clock)) :=
  (providerTracks context).publicCheck (CommitmentBoundary.checker context.commitments)

private theorem completeVerifier (context : Context) : Tracks context (base context) :=
  ((declarationTracks context).publicCheck
    (HostHintTarget.checker context.source.host context.target.host (Address.toNat (publicCursor context).head))).publicCheck
    (ResourceBoundary.checker context.limits context.source context.target)

theorem verifier_split (context : Context) (env : Environment Fp) (channel : RawChannel Fp) :
    ∃ first last, ∀ clock, (base context clock).verifierOperations.interactionValuesWith channel env =
      first ++ (if channel = HostHintQueue.stateChannel.toRaw then
        [HostHintQueue.stateChannel.pulledValue (context.withClock clock).finalHints] else []) ++ last :=
  (completeVerifier context).ledger env channel

end SP1Clean.Export.InstalledAssembly
