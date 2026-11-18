import SP1Clean.Soundness.ProtectedLocalCore
import SP1Clean.Soundness.LocalCoreLookups
import ToClean.Air.ComponentReplacement

/-! # Component layout of the protected local tables

The first 61 protected tables are the local core's components, with the four store chips replaced
by their permission wrappers; the permission request and fixed membership tables follow. The host
assembly reads its original components through `component_projection`/`component_layout`, and the
two permission channels are fresh for every local-core channel.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Resolve a protected component without unfolding the complete physical inventory. -/
theorem tables_getElem (image : ProgramImage) (source : ExecutionSnapshot)
    (index : ℕ) (bound : index < 61) :
    (tables (p := p) image source)[index]'(by rw [tables_length]; omega) =
      if 28 = index then { circuit := ProtectedStore.double, Assumptions := (ProtectedStore.double).Assumptions, generation := StoreDoubleChip.generation } else
      if 27 = index then { circuit := ProtectedStore.word, Assumptions := (ProtectedStore.word).Assumptions, generation := StoreWordChip.generation } else
      if 26 = index then { circuit := ProtectedStore.half, Assumptions := (ProtectedStore.half).Assumptions, generation := StoreHalfChip.generation } else
      if 25 = index then { circuit := ProtectedStore.byte, Assumptions := (ProtectedStore.byte).Assumptions, generation := StoreByteChip.generation } else
      (LocalCore.tables image source)[index]'(by rw [LocalCore.tables_length]; exact bound) := by
  simp only [tables]
  rw [List.getElem_append_left (by
    simpa only [List.length_set, LocalCore.tables_length] using bound)]
  simp only [List.getElem_set]

/-- Each retained component preserves its original local algebra and old channel ledgers. -/
theorem component_projection (image : ProgramImage) (source : ExecutionSnapshot)
    (index : Fin 61) :
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

/-- Permission interactions preserve physical widths and fixed-row contracts. -/
theorem component_layout (image : ProgramImage) (source : ExecutionSnapshot) (index : Fin 61) :
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact index.isLt)
    let extended := (tables (p := p) image source)[index.val]'(by rw [tables_length]; omega)
    original.width = extended.width ∧ original.FixedRowsMatch = extended.FixedRowsMatch := by
  -- Keep the predicate folded while rewriting the dependent component and its instances.
  let layout (original extended : Component (ZMod p)) : Prop :=
    original.width = extended.width ∧ original.FixedRowsMatch = extended.FixedRowsMatch
  change layout _ _
  rw [tables_getElem image source index.val index.isLt]
  rcases index with ⟨index, bound⟩
  dsimp only
  split_ifs with double word half byte
  · subst index; exact ⟨ProtectedStore.double_width.symm, rfl⟩
  · subst index; exact ⟨ProtectedStore.word_width.symm, rfl⟩
  · subst index; exact ⟨ProtectedStore.half_width.symm, rfl⟩
  · subst index; exact ⟨ProtectedStore.byte_width.symm, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem old_channel_ne_permission {image : ProgramImage} {source : ExecutionSnapshot}
    (channel : RawChannel (ZMod p)) (member : channel ∈ (LocalCore.ensemble image source).channels) :
    channel ≠ WritePermissionProvider.channel.toRaw := by
  change channel ∈ (LocalCore.baseEnsemble image source).channels ++ [LocalCore.sourceChannel image source] at member
  rcases List.mem_append.mp member with member | member
  · rintro rfl
    exact LocalCore.not_mem_baseEnsemble_channels
      (by simp [LocalCore.baseChannelNames, WritePermissionProvider.channel, Channel.toRaw]) member
  · obtain rfl := List.mem_singleton.mp member
    exact VerifierChannel.channel_ne_of_not_prefix "sp1.local.source" _ (by
      simp only [WritePermissionProvider.channel, Channel.toRaw]; decide)

/-- The interval-membership channel is fresh for every registered local-core channel. -/
theorem old_channel_ne_membership {image : ProgramImage} {source : ExecutionSnapshot}
    (channel : RawChannel (ZMod p)) (member : channel ∈ (LocalCore.ensemble image source).channels) :
    channel ≠ image.writePermissionTable.channel.toRaw := by
  change channel ∈ (LocalCore.baseEnsemble image source).channels ++ [LocalCore.sourceChannel image source] at member
  rcases List.mem_append.mp member with member | member
  · rintro rfl
    exact LocalCore.not_mem_baseEnsemble_channels (by
      simp [LocalCore.baseChannelNames, StaticTable.channel, ProgramImage.writePermissionTable,
        StaticTable.ofRows, Channel.toRaw]) member
  · obtain rfl := List.mem_singleton.mp member
    exact VerifierChannel.channel_ne_of_not_prefix "sp1.local.source" _ (by
      simp only [StaticTable.channel, ProgramImage.writePermissionTable, StaticTable.ofRows, Channel.toRaw]
      decide)

end SP1Clean.Soundness.ProtectedLocalCore
