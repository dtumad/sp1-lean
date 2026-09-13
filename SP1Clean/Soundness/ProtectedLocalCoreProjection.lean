import SP1Clean.Soundness.ProtectedLocalCore
import ToClean.Air.EnsembleProjection

/-! # The protected local AIR retains the original execution witness

The first 59 physical tables are reinterpreted by their original components; the fixed permission
provider is omitted. Assertions, lookups, prover data, public input, and every original channel's
complete interaction list are preserved. Thus all previously proved local ordering and grounding
results apply to this projection without additional validity or balance premises.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem tables_getElem (image : ProgramImage) (source : ExecutionSnapshot)
    (index : ℕ) (bound : index < 59) :
    (tables (p := p) image source)[index]'(by rw [tables_length]; omega) =
      if 28 = index then ⟨ProtectedStore.double⟩ else
      if 27 = index then ⟨ProtectedStore.word⟩ else
      if 26 = index then ⟨ProtectedStore.half⟩ else
      if 25 = index then ⟨ProtectedStore.byte⟩ else
      (LocalCore.tables image source)[index]'(by rw [LocalCore.tables_length]; exact bound) := by
  simp only [tables]
  rw [List.getElem_append_left (by
    simpa only [List.length_set, LocalCore.tables_length] using bound)]
  simp only [List.getElem_set]

/-- Each retained component preserves its original local algebra and old channel ledgers. -/
theorem component_projection (image : ProgramImage) (source : ExecutionSnapshot)
    (index : Fin 59) :
    let extended := (tables (p := p) image source)[index.val]'(by rw [tables_length]; omega)
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact index.isLt)
    extended.operations.constraints = original.operations.constraints ∧
    extended.operations.lookups = original.operations.lookups ∧
    ∀ channel, channel ≠ WritePermissionProvider.channel.toRaw →
      extended.operations.interactionsWith channel = original.operations.interactionsWith channel := by
  dsimp only
  rw [tables_getElem image source index.val index.isLt]
  rcases index with ⟨index, bound⟩
  dsimp only
  by_cases double : 28 = index
  · subst index
    simp only [↓reduceIte]
    exact ⟨ProtectedStore.double_constraints, ProtectedStore.double_lookups, ProtectedStore.double_interactions⟩
  by_cases word : 27 = index
  · subst index
    simp only [↓reduceIte]
    exact ⟨ProtectedStore.word_constraints, ProtectedStore.word_lookups, ProtectedStore.word_interactions⟩
  by_cases half : 26 = index
  · subst index
    simp only [↓reduceIte]
    exact ⟨ProtectedStore.half_constraints, ProtectedStore.half_lookups, ProtectedStore.half_interactions⟩
  by_cases byte : 25 = index
  · subst index
    simp only [↓reduceIte]
    exact ⟨ProtectedStore.byte_constraints, ProtectedStore.byte_lookups, ProtectedStore.byte_interactions⟩
  simp [double, word, half, byte]

private theorem projectionLength (image : ProgramImage) (source : ExecutionSnapshot) :
    (LocalCore.ensemble (p := p) image source).tables.length ≤ (ensemble (p := p) image source).tables.length := by
  change (LocalCore.tables (p := p) image source).length ≤ (tables (p := p) image source).length
  rw [LocalCore.tables_length, tables_length]
  decide

/-- The original witness uses exactly the same source, public input, prover data, and row arrays. -/
def localWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness (LocalCore.ensemble (p := p) image source) :=
  witness.project (LocalCore.ensemble image source) (projectionLength image source)

theorem localWitness_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) : (localWitness witness).Constraints := by
  apply witness.project_constraints (target := LocalCore.ensemble image source)
    (projectionLength image source) rfl ?_ ?_ constraints
  · intro index
    exact (component_projection image source ⟨index.val, by
      simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).1.symm
  · intro index
    exact (component_projection image source ⟨index.val, by
      simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).2.1.symm

private theorem provider_suffix_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channel : RawChannel (ZMod p)) (different : channel ≠ WritePermissionProvider.channel.toRaw) :
    (witness.tables.drop 59).flatMap (·.interactionsWith channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_drop, witness.tables_map_component] at mapped
  change table.component ∈ (tables image source).drop 59 at mapped
  have length : ((((LocalCore.tables (p := p) image source).set 25 ⟨ProtectedStore.byte⟩).set 26
      ⟨ProtectedStore.half⟩).set 27 ⟨ProtectedStore.word⟩ |>.set 28 ⟨ProtectedStore.double⟩).length = 59 := by
    simp only [List.length_set, LocalCore.tables_length]
  rw [tables, List.drop_left' length] at mapped
  obtain same := List.mem_singleton.mp mapped
  apply table.interactionsWith_nil_of_channel_not_mem
  rw [same]
  change channel ∉ [WritePermissionProvider.channel.toRaw]
  simpa only [List.mem_singleton] using different

/-- Retaining the old components also retains each complete pre-existing channel ledger. -/
theorem localWitness_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channel : RawChannel (ZMod p)) (different : channel ≠ WritePermissionProvider.channel.toRaw) :
    (localWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  apply witness.project_interactions (target := LocalCore.ensemble image source)
    (projectionLength image source) rfl channel ?_ ?_
  · intro index
    exact ((component_projection image source ⟨index.val, by
      simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).2.2 channel different).symm
  · change (witness.tables.drop (LocalCore.tables image source).length).flatMap _ = []
    rw [LocalCore.tables_length]
    exact provider_suffix_silent witness channel different

theorem old_channel_ne_permission {image : ProgramImage} {source : ExecutionSnapshot}
    (channel : RawChannel (ZMod p)) (member : channel ∈ (LocalCore.ensemble image source).channels) :
    channel ≠ WritePermissionProvider.channel.toRaw := by
  intro same
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  rw [same] at names
  simp [LocalCore.ensemble, sp1Ensemble_channels, OrderedBoundary.channel,
    SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
    WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel, programChannel,
    exitChannel, syscallChannel, publicValuesChannel, Channel.toRaw] at names

/-- The protected ensemble supplies all balance premises of the original local grounding. -/
theorem localWitness_balanced {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (balanced : witness.BalancedChannels) : (localWitness witness).BalancedChannels := by
  intro channel member
  change BalancedInteractions ((localWitness witness).interactionsWith channel)
  rw [localWitness_interactions witness channel (old_channel_ne_permission channel member)]
  exact balanced channel (List.mem_cons_of_mem _ member)

/-- The protected AIR refines the original local AIR at the same public boundary. -/
theorem statement_implies_local (image : ProgramImage) (source : ExecutionSnapshot)
    (publicInput : SP1PublicIO (ZMod p))
    (statement : (ensemble image source).Statement publicInput) :
    (LocalCore.ensemble image source).Statement publicInput := by
  obtain ⟨witness, publicEq, constraints, balanced⟩ := statement
  exact ⟨localWitness witness, publicEq, localWitness_constraints witness constraints,
    localWitness_balanced witness balanced⟩

end SP1Clean.Soundness.ProtectedLocalCore
