import SP1Clean.Soundness.HostObservedLedger

/-! # Byte authentication for the installed ordinary consumer

The receipt-producing replacement preserves the complete Byte ledger and its verifier prefix.
The table occurrences therefore inherit the Byte facts of the complete-memory assembly.
-/

namespace SP1Clean.Soundness.HostObserved

open Circuit Air.Flat Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

private theorem byteRegistered :
    byteChannel.toRaw ∈ (HostFinalMemory.Installed image source target final).channels := by
  apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  simp [HostLocalCore.baseEnsemble, HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels]

attribute [local irreducible] HostFinalMemory.ensemble

omit [Fact (2 ^ 25 < p)] in
private theorem verifier_iff (ens : Ensemble (ZMod p) SP1PublicIO) (data : ProverData (ZMod p)) :
    ens.VerifierChannelRequirements data byteChannel.toRaw ↔ ∀ i ∈ ens.verifierOperations.interactionValuesWith
      byteChannel.toRaw data.publicEnvironment, i.Requirements data := by
  simp only [Ensemble.VerifierChannelRequirements, Operations.ChannelRequirements,
    Operations.forall_interactionsWith_iff, Operations.interactionValuesWith_eq_map, List.forall_mem_map]
  rfl

/-- Both public checks added to the host supervisor leave its genuine Byte verifier ledger intact. -/
theorem verifier_byte_requirements (data : ProverData (ZMod p)) :
    (ensemble image source target final).VerifierChannelRequirements data byteChannel.toRaw := by
  let original := HostFinalMemory.Installed image source target final
  have registered : byteChannel.toRaw ∈ original.channels := byteRegistered
  have different : byteChannel.toRaw ≠ (SP1Clean.OrdinaryObservation.stateChannel (p := p)).toRaw := by
    simp [byteChannel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]
  have physical : (ensemble image source target final).verifierOperations.interactionValuesWith byteChannel.toRaw data.publicEnvironment =
      original.verifierOperations.interactionValuesWith byteChannel.toRaw data.publicEnvironment := by
    rw [verifier_interactions, ite_eq_right different, List.append_nil]
    exact (SailBoundary.checker source target).install_verifier_interactions_of_mem original _ _ registered
  have prior : original.VerifierChannelRequirements data byteChannel.toRaw := by
    intro i mem _
    exact HostFinalMemory.verifier_requirements (image := image) (source := source) (target := target.sail.memorySnapshot)
      (final := final) (bankFinal := target.host) (others := HostCallReceivers.available)
      (resources := HostHintReadLocal.sourceResources source.host.io.hints) (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
      (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)
      (registration := HostFinalMemory.source_registration image source target.sail.memorySnapshot) _ i mem
  rw [verifier_iff, physical]
  exact (verifier_iff original data).mp prior

/-- Each original observed component satisfies its outgoing Byte requirements, independently
of the other consumers sharing the final physical Byte ledger. -/
theorem component_byte_requirements (component : Component (ZMod p))
    (member : component ∈ (ensemble image source target final).tables) (env : Environment (ZMod p))
    (checked : component.operations.ConstraintsHold env) : component.operations.ChannelRequirements byteChannel.toRaw env := by
  simp only [ensemble, ClosedVerifier.withInteractions] at member
  obtain ⟨old, included, constraints, lookups, traffic⟩ := HostOrdinaryReceipts.original_of_mem
    (image := image) (source := source) (target := target) (final := final) (others := HostCallReceivers.available)
    (resources := HostHintReadLocal.sourceResources source.host.io.hints)
    (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) component member
  have before : old ∈ (HostFinalMemory.Installed image source target final).tables := included
  have valid : old.operations.ConstraintsHold env := by simpa only [Operations.ConstraintsHold, constraints, lookups] using checked
  apply Operations.channelRequirements_of_interactionsWith_subset _ _ _ _ env
    (HostFinalMemory.component_byte_requirements (image := image) (source := source) (target := target.sail.memorySnapshot)
      (final := final) (bankFinal := target.host) (others := HostCallReceivers.available)
      (resources := HostHintReadLocal.sourceResources source.host.io.hints) (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
      (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)
      (registration := HostFinalMemory.source_registration image source target.sail.memorySnapshot)
      (HostHintReadLocal.source_interface source.host.io.hints) old before env valid)
  rw [traffic _ (by simp [byteChannel, InstructionReceipt.channel, Channel.toRaw])]

private theorem registered_observed : byteChannel.toRaw ∈ (ensemble image source target final).channels :=
  List.mem_append_left _ (byteRegistered (image := image) (source := source) (target := target) (final := final))

attribute [local irreducible] ensemble

/-- The Byte guarantees of the original host inventory hold for every observed physical table. -/
theorem byte_guarantees (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (funded : DeclarationsOpen witness) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees byteChannel.toRaw := by
  have balanced := funded _ registered_observed (by simp [byteChannel, CommitmentDeclaration.channel, Channel.toRaw])
  exact (witness.channelGuarantees_of_component_requirements _ checked balanced
    (verifier_byte_requirements (image := image) (source := source) (target := target) (final := final))
    (component_byte_requirements (image := image) (source := source) (target := target) (final := final))).2

/-- Raw constraints and balance establish the row specification of the installed guarded consumer. -/
theorem consumer_spec (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (funded : DeclarationsOpen witness) :
    ((observationSlot 0).table witness).Spec := by
  let slot := observationSlot (image := image) (source := source) (target := target) (final := final) 0
  let table := slot.table witness
  have component : table.component = OrdinaryObservation.consumer := slot.table_component witness
  have constraints := slot.table_constraints witness checked
  have byte := slot.table_channelGuarantees witness byteChannel.toRaw (byte_guarantees witness checked funded)
  intro row member
  have valid := constraints row member
  have authentic := byte row member
  change table.component.Spec (table.environment row)
  rw [component] at valid authentic ⊢
  have assumptions : OrdinaryObservation.consumer.CircuitAssumptions (table.environment row) := by
    intro _
    trivial
  apply (Component.weakSoundness assumptions valid ?_).1
  rw [Operations.guarantees_iff _ _ _ (OrdinaryObservation.consumer.inChannelsOrGuarantees (table.environment row))]
  intro channel present
  have member := OrdinaryObservation.consumer_channels
    (List.mem_append_left _ present)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact authentic
  · exact Operations.channelGuarantees_of_trivial _ (by simp [InstructionReceipt.channel, Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]) _ _

end SP1Clean.Soundness.HostObserved
