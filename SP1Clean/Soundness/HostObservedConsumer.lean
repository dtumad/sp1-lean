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

private theorem canonicalData (witness : EnsembleWitness (ensemble image source target final)) :
    (baseWitness witness).data = witness.data := by
  let receipts : EnsembleWitness (producers image source target final) :=
    witness.withEnsemble _ (by simp only [ensemble, ClosedVerifier.withInteractions])
  change (HostOrdinaryReceipts.baseWitness receipts).data = receipts.data
  exact HostOrdinaryReceipts.baseWitness_data receipts

attribute [local irreducible] ensemble

/-- The Byte guarantees of the original host inventory hold for every observed physical table. -/
theorem byte_guarantees (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (funded : DeclarationsOpen witness) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees byteChannel.toRaw := by
  let original := HostFinalMemory.Installed image source target final
  let projected := baseWitness witness
  have registered : byteChannel.toRaw ∈ original.channels := byteRegistered
  have outside : byteChannel.toRaw ∉ HostFinalMemory.externalChannels (p := p) := by
    simp [HostFinalMemory.externalChannels, byteChannel, InstructionReceipt.channel,
      SP1Clean.OrdinaryObservation.stateChannel, CommitmentDeclaration.channel, Channel.toRaw]
  have receipt : byteChannel.toRaw ≠ (InstructionReceipt.channel (p := p)).toRaw := by
    simp [byteChannel, InstructionReceipt.channel, Channel.toRaw]
  have observation : byteChannel.toRaw ≠ (SP1Clean.OrdinaryObservation.stateChannel (p := p)).toRaw := by
    simp [byteChannel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]
  have base := HostFinalMemory.byte_guarantees projected (HostHintReadLocal.source_interface source.host.io.hints)
    (baseWitness_constraints witness checked) (grounding_balance witness funded _ registered outside)
  have data : projected.data = witness.data := canonicalData witness
  have verifier : witness.verifierInteractionsWith byteChannel.toRaw =
      projected.verifierInteractionsWith byteChannel.toRaw := by
    change (ensemble image source target final).verifierOperations.interactionValuesWith _ _ =
      original.verifierOperations.interactionValuesWith _ projected.data.publicEnvironment
    rw [data, verifier_interactions, ite_eq_right observation, List.append_nil]
    exact (SailBoundary.checker source target).install_verifier_interactions_of_mem original _ _ registered
  have ledger := baseWitness_interactions witness byteChannel.toRaw registered receipt observation
  change projected.verifierInteractionsWith byteChannel.toRaw ++ projected.tables.flatMap (·.interactionsWith byteChannel.toRaw) =
    witness.verifierInteractionsWith byteChannel.toRaw ++ witness.tables.flatMap (·.interactionsWith byteChannel.toRaw) at ledger
  rw [verifier, List.append_right_inj] at ledger
  intro table member
  rw [Table.channelGuarantees_iff_forall]
  intro interaction emitted
  have physical : interaction ∈ projected.tables.flatMap (·.interactionsWith byteChannel.toRaw) := by
    rw [ledger]
    exact List.mem_flatMap.mpr ⟨table, member, emitted⟩
  obtain ⟨previous, earlier, occurrence⟩ := List.mem_flatMap.mp physical
  have authenticated := (previous.channelGuarantees_iff_forall byteChannel.toRaw).mp
    (base previous earlier) interaction occurrence
  have before : previous.data = projected.data := projected.same_data previous earlier
  have after : table.data = witness.data := witness.same_data table member
  rwa [before, data, ← after] at authenticated

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
