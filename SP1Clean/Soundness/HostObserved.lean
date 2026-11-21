import SP1Clean.Soundness.HostOrdinaryReceipts
import SP1Clean.Soundness.HostFinalMemoryDeclarations
import SP1Clean.Soundness.HostFinalMemoryLookups
import SP1Clean.Native.Operations.OrdinaryObservationEndpoint

/-! # Installed ordinary receipts and verifier-owned observation endpoints

Instruction rows publish their gated successor receipts in the original physical positions.
The supplied snapshots fix the observation start and the final sentinel. Projecting a witness
forgets only the new receipt and observation traffic and the checked Sail boundary.
-/

namespace SP1Clean.Soundness.HostObserved

open Circuit Air.Flat Channels Semantics
open scoped Classical
open SP1Clean.OrdinaryObservation (startFor finalFor endpoint)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Protected instruction producers in the six-call assembly with its static Sail target check. -/
abbrev producers (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) :=
  HostOrdinaryReceipts.ensemble image source target final HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) (HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)

private theorem base_external_registered (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (channel : RawChannel (ZMod p))
    (member : channel ∈ HostFinalMemory.externalChannels (p := p)) :
    channel ∈ (HostFinalMemory.Installed image source target final).channels := by
  change _ ∈ (_ ++ [_]) ++ [_]
  apply List.mem_append_left _ (List.mem_append_left _ ?_)
  change _ ∈ _ ++ [_]
  apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (HostFinalMemory.external_registered _ member))

private theorem endpoint_registered (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) :
    (endpoint (startFor source.sail) (finalFor source.sail target.sail)).circuit.channels ⊆
      (producers image source target final).channels := by
  intro channel used
  simp only [endpoint, SP1Clean.OrdinaryObservation.endpointCircuit, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at used
  subst channel
  exact List.mem_append_left _ (base_external_registered image source target final _ (by simp [HostFinalMemory.externalChannels]))

/-- Install the observation start and final links on the existing verifier and channel registry. -/
def ensemble (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) : Ensemble (ZMod p) SP1PublicIO :=
  (endpoint (startFor source.sail) (finalFor source.sail target.sail)).withInteractions
    (producers image source target final) (endpoint_registered image source target final)

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

/-- Every original physical component keeps its name and position. -/
theorem table_names :
    (ensemble image source target final).tables.map (·.circuit.name) =
      (HostFinalMemory.Installed image source target final).tables.map (·.circuit.name) := by
  simp only [ensemble, ClosedVerifier.withInteractions]
  exact HostOrdinaryReceipts.table_names (image := image) (source := source) (target := target)
    (final := final) (others := HostCallReceivers.available) (resources := HostHintReadLocal.sourceResources source.host.io.hints)
    (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)

/-- Installing the ordinary receipts and endpoints preserves all external host channels. -/
theorem external_registered {channel : RawChannel (ZMod p)} (external : channel ∈ HostFinalMemory.externalChannels) :
    channel ∈ (ensemble image source target final).channels :=
  List.mem_append_left _ (base_external_registered image source target final channel external)

/-- The immutable commitment provider's channel is registered in the observed assembly. -/
theorem declarationsRegistered :
    CommitmentDeclaration.channel.toRaw ∈ (ensemble image source target final).channels :=
  external_registered (by simp [HostFinalMemory.externalChannels])

/-- Receipt publication preserves the absence of legacy lookups in every physical component. -/
theorem lookupFree : LookupFree (ensemble image source target final).tables := by
  intro component member
  simp only [ensemble, ClosedVerifier.withInteractions] at member
  obtain ⟨original, included, _, lookups, _⟩ := HostOrdinaryReceipts.original_of_mem (image := image) (source := source) (target := target) (final := final) (others := HostCallReceivers.available)
    (resources := HostHintReadLocal.sourceResources source.host.io.hints) (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) component member
  exact lookups.trans (HostFinalMemory.installed_lookupFree (image := image) (source := source) (target := target) (final := final) original included)

/-- Declaration pushes still have their original authenticated meaning. -/
theorem declaration_sources (property : CommitmentDeclaration.Row (ZMod p) → Prop)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source target final).tables) :
    component.Authenticates CommitmentDeclaration.channel property := by
  simp only [ensemble, ClosedVerifier.withInteractions] at member
  obtain ⟨original, included, constraints, lookups, ledger⟩ := HostOrdinaryReceipts.original_of_mem (image := image) (source := source) (target := target) (final := final) (others := HostCallReceivers.available)
    (resources := HostHintReadLocal.sourceResources source.host.io.hints) (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) component member
  intro env checked interaction traffic push
  have same := ledger CommitmentDeclaration.channel.toRaw (by
    simp [CommitmentDeclaration.channel, InstructionReceipt.channel, Channel.toRaw])
  rw [Operations.ConstraintsHold, constraints, lookups] at checked
  rw [Operations.interactionValuesWith, same] at traffic
  exact HostFinalMemory.declaration_sources (image := image) (source := source) (target := target) (final := final)
    property original included env checked interaction traffic push

/-- The observed verifier adds exactly the start and final occurrences on its private channel. -/
theorem verifier_interactions (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    (ensemble image source target final).verifierOperations.interactionValuesWith channel env =
      (producers image source target final).verifierOperations.interactionValuesWith channel env ++
        (if channel = SP1Clean.OrdinaryObservation.stateChannel.toRaw then
          [SP1Clean.OrdinaryObservation.stateChannel.pushedValue (startFor source.sail),
           SP1Clean.OrdinaryObservation.stateChannel.pulledValue (finalFor source.sail target.sail)] else []) := by
  let bound := endpoint (p := p) (startFor source.sail) (finalFor source.sail target.sail)
  change ((producers image source target final).verifier.andThen bound.interactionProgram).circuitOperations.interactionValuesWith channel env = _
  rw [Verifier.Program.andThen_values]
  congr 1
  change bound.emit.circuitOperations.interactionValuesWith channel env = _
  rw [ClosedVerifier.emit_values]
  exact SP1Clean.OrdinaryObservation.endpoint_values _ _ 0 _ channel

/-- For an external protocol, only the final observation endpoint can contribute verifier traffic. -/
theorem verifier_external (env : Environment (ZMod p)) (channel : RawChannel (ZMod p))
    (outside : channel ∈ HostFinalMemory.externalChannels (p := p)) :
    (ensemble image source target final).verifierOperations.interactionValuesWith channel env =
      if channel = SP1Clean.OrdinaryObservation.stateChannel.toRaw then
        [SP1Clean.OrdinaryObservation.stateChannel.pushedValue (startFor source.sail),
         SP1Clean.OrdinaryObservation.stateChannel.pulledValue (finalFor source.sail target.sail)] else [] := by
  let original := HostFinalMemory.Installed image source target final
  have silent : (producers image source target final).verifierOperations.interactionValuesWith channel env = [] := by
    change ((SailBoundary.checker source target).install original).verifierOperations.interactionValuesWith channel env = []
    rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ (base_external_registered image source target final channel outside)]
    exact HostFinalMemory.verifier_external_silent outside env
  rw [verifier_interactions, silent, List.nil_append]

/-- Commitment declarations remain silent in every verifier layer of the installed assembly. -/
theorem verifier_declarations_silent (env : Environment (ZMod p)) :
    (ensemble image source target final).verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = [] := by
  rw [verifier_external _ _ (by simp [HostFinalMemory.externalChannels]),
    ite_eq_right (by simp [CommitmentDeclaration.channel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw])]

private def producerWitness (witness : EnsembleWitness (ensemble image source target final)) :
    EnsembleWitness (producers image source target final) := witness.withEnsemble _ (by simp only [ensemble, ClosedVerifier.withInteractions])

private theorem producerWitness_interactions (witness : EnsembleWitness (ensemble image source target final))
    (channel : RawChannel (ZMod p)) (different : channel ≠ SP1Clean.OrdinaryObservation.stateChannel.toRaw) :
    (producerWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  change _ = (ensemble image source target final).verifierOperations.interactionValuesWith channel
    witness.data.publicEnvironment ++ _
  rw [verifier_interactions, ite_eq_right different, List.append_nil]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith, EnsembleWitness.toTables,
    EnsembleWitness.data, producerWitness, EnsembleWitness.withEnsemble]

/-- The original complete-memory assembly sees the same witness rows and public header. -/
def baseWitness (witness : EnsembleWitness (ensemble image source target final)) :
    EnsembleWitness (HostFinalMemory.Installed image source target final) :=
  HostSailBoundary.baseWitness (HostOrdinaryReceipts.baseWitness (producerWitness witness))

/-- Projection retains the complete header. -/
theorem baseWitness_publicInput (witness : EnsembleWitness (ensemble image source target final)) :
    (baseWitness witness).publicInput = witness.publicInput := by
  simp only [baseWitness, HostSailBoundary.baseWitness, PublicVerifier.project, EnsembleWitness.withEnsemble]
  rw [HostOrdinaryReceipts.baseWitness_publicInput (producerWitness witness)]
  simp only [producerWitness, EnsembleWitness.withEnsemble]

/-- Projection retains every original row check. -/
theorem baseWitness_constraints (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) : (baseWitness witness).Constraints := by
  apply HostSailBoundary.baseWitness_constraints (HostOrdinaryReceipts.baseWitness (producerWitness witness))
  apply HostOrdinaryReceipts.baseWitness_constraints (producerWitness witness)
  simpa only [EnsembleWitness.Constraints, producerWitness, EnsembleWitness.withEnsemble] using checked

/-- Every original ledger except the two observation protocols remains literally unchanged. -/
theorem baseWitness_interactions (witness : EnsembleWitness (ensemble image source target final))
    (channel : RawChannel (ZMod p)) (registered : channel ∈ (HostFinalMemory.Installed image source target final).channels)
    (receipt : channel ≠ InstructionReceipt.channel.toRaw) (observation : channel ≠ SP1Clean.OrdinaryObservation.stateChannel.toRaw) :
    (baseWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  let sail := HostOrdinaryReceipts.baseWitness (producerWitness witness)
  let original := HostFinalMemory.Installed image source target final
  let check := SailBoundary.checker (p := p) source target
  change (check.project (ens := original) sail).interactionsWith channel = _
  rw [check.project_interactions sail channel (fun eq => check.channel_not_mem original (eq ▸ registered))]
  exact (HostOrdinaryReceipts.baseWitness_interactions _ channel receipt).trans
    (producerWitness_interactions witness channel observation)

/-- Declaration requests of the grounded execution are also requests in the observed ledger. -/
theorem baseWitness_declarations (witness : EnsembleWitness (ensemble image source target final)) :
    (baseWitness witness).interactionsWith CommitmentDeclaration.channel.toRaw =
      witness.interactionsWith CommitmentDeclaration.channel.toRaw :=
  baseWitness_interactions witness _ (base_external_registered image source target final _ (by simp [HostFinalMemory.externalChannels]))
    (by simp [CommitmentDeclaration.channel, InstructionReceipt.channel, Channel.toRaw])
    (by simp [CommitmentDeclaration.channel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw])

/-- Only the outer verifier-owned commitment provider has been projected away. -/
def DeclarationsOpen (witness : EnsembleWitness (ensemble image source target final)) : Prop :=
  ∀ channel ∈ (ensemble image source target final).channels,
    channel ≠ CommitmentDeclaration.channel.toRaw → witness.BalancedChannel channel

/-- The original host proof obtains balance on every channel it consumes. -/
theorem grounding_balance (witness : EnsembleWitness (ensemble image source target final))
    (balanced : DeclarationsOpen witness) : HostFinalMemory.ExternallyBalanced (baseWitness witness) := by
  intro channel registered external
  have neq (other) (member : other ∈ HostFinalMemory.externalChannels (p := p)) : channel ≠ other :=
    fun eq => external (eq ▸ member)
  change BalancedInteractions ((baseWitness witness).interactionsWith channel)
  rw [baseWitness_interactions witness channel registered
    (neq _ (by simp [HostFinalMemory.externalChannels])) (neq _ (by simp [HostFinalMemory.externalChannels]))]
  exact balanced _ (List.mem_append_left _ registered) (neq _ (by simp [HostFinalMemory.externalChannels]))

/-- The Sail checker in this same assembly authenticates the supplied snapshot frame and endpoints. -/
theorem target_spec (witness : EnsembleWitness (ensemble image source target final))
    (balanced : DeclarationsOpen witness) : SailBoundary.Spec source target witness.publicInput := by
  let check := SailBoundary.checker (p := p) source target
  let original := HostFinalMemory.Installed image source target final
  let selected := check.channel original
  have fresh (channel) (registered : channel ∈ original.channels) : selected ≠ channel :=
    fun eq => check.channel_not_mem original (show selected ∈ original.channels from eq ▸ registered)
  have outside (channel) (registered : channel ∈ HostFinalMemory.externalChannels (p := p)) :
      selected ≠ channel := fresh _ (base_external_registered image source target final _ registered)
  let sail := HostOrdinaryReceipts.baseWitness (producerWitness witness)
  have h := balanced selected (List.mem_append_right _ (List.mem_singleton_self selected))
    (outside _ (by simp [HostFinalMemory.externalChannels]))
  change BalancedInteractions (witness.interactionsWith selected) at h
  rw [← producerWitness_interactions witness selected (outside _ (by simp [HostFinalMemory.externalChannels])),
      ← HostOrdinaryReceipts.baseWitness_interactions _ selected (outside _ (by simp [HostFinalMemory.externalChannels]))] at h
  have same : sail.interactionsWith selected = _ := check.installed_check_interactions (ens := original) sail
  change BalancedInteractions (sail.interactionsWith selected) at h
  rw [same] at h
  have spec := (SailBoundary.checks_iff source target sail.publicInput sail.data).mp
    ((check.program_balanced_iff original _ _).mp h)
  simpa only [sail, HostOrdinaryReceipts.baseWitness_publicInput, producerWitness, EnsembleWitness.withEnsemble] using spec

end SP1Clean.Soundness.HostObserved
