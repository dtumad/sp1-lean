import SP1Clean.Soundness.ProtectedLocalCore
import SP1Clean.Soundness.LocalCoreLookups
import ToClean.Air.ComponentReplacement

/-! # The protected local AIR retains the original execution witness

The first 59 physical tables are reinterpreted by their original components; the fixed permission
provider is omitted. Assertions, lookups, public input, and every original channel's complete
interaction list are preserved. Canonical data agrees at every key except the removed provider.
Thus all previously proved local ordering and grounding results apply to this projection without
additional validity or balance premises.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem tables_getElem (image : ProgramImage) (source : ExecutionSnapshot)
    (index : ℕ) (bound : index < 59) :
    (tables (p := p) image source)[index]'(by rw [tables_length]; omega) =
      if 28 = index then { circuit := ProtectedStore.double } else
      if 27 = index then { circuit := ProtectedStore.word } else
      if 26 = index then { circuit := ProtectedStore.half } else
      if 25 = index then { circuit := ProtectedStore.byte } else
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

/-- Permission interactions do not alter row layouts, data keys, or input encoding. -/
theorem component_layout (image : ProgramImage) (source : ExecutionSnapshot) (index : Fin 59) :
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact index.isLt)
    let extended := (tables (p := p) image source)[index.val]'(by rw [tables_length]; omega)
    original.width = extended.width ∧ original.fixedColumns = extended.fixedColumns ∧
    original.circuit.name = extended.circuit.name ∧
    ∀ rows arity, original.proverRows rows arity = extended.proverRows rows arity := by
  -- Keep the predicate folded while rewriting the dependent component and its instances.
  let layout (original extended : Component (ZMod p)) : Prop :=
    original.width = extended.width ∧ original.fixedColumns = extended.fixedColumns ∧
      original.circuit.name = extended.circuit.name ∧
        ∀ rows arity, original.proverRows rows arity = extended.proverRows rows arity
  change layout _ _
  rw [tables_getElem image source index.val index.isLt]
  rcases index with ⟨index, bound⟩
  dsimp only
  split_ifs with double word half byte
  · subst index; exact ⟨ProtectedStore.double_width.symm, rfl, rfl, fun _ _ => rfl⟩
  · subst index; exact ⟨ProtectedStore.word_width.symm, rfl, rfl, fun _ _ => rfl⟩
  · subst index; exact ⟨ProtectedStore.half_width.symm, rfl, rfl, fun _ _ => rfl⟩
  · subst index; exact ⟨ProtectedStore.byte_width.symm, rfl, rfl, fun _ _ => rfl⟩
  · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

private theorem projectionLength (image : ProgramImage) (source : ExecutionSnapshot) :
    (LocalCore.ensemble (p := p) image source).tables.length ≤ (ensemble (p := p) image source).tables.length := by
  change (LocalCore.tables (p := p) image source).length ≤ (tables (p := p) image source).length
  rw [LocalCore.tables_length, tables_length]
  decide

private theorem projectionWidth (image : ProgramImage) (source : ExecutionSnapshot)
    (index : Fin (LocalCore.ensemble (p := p) image source).tables.length) :
    (LocalCore.ensemble image source).tables[index.val].width =
      ((ensemble image source).tables[index.val]'(by have := projectionLength (p := p) image source; omega)).width :=
  (component_layout image source ⟨index.val, by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).1

private theorem projectionFixed (image : ProgramImage) (source : ExecutionSnapshot)
    (index : Fin (LocalCore.ensemble (p := p) image source).tables.length) :
    (LocalCore.ensemble image source).tables[index.val].fixedColumns =
      ((ensemble image source).tables[index.val]'(by have := projectionLength (p := p) image source; omega)).fixedColumns :=
  (component_layout image source ⟨index.val, by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).2.1

/-- Project the same physical rows and public boundary; canonical data drops the permission key. -/
def localWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness (LocalCore.ensemble (p := p) image source) :=
  witness.projectPrefix (LocalCore.ensemble image source) (projectionLength image source)
    (fun index => (projectionWidth image source index).le) (projectionFixed image source)

/-- Each projected table retains its complete physical arrays under the original component. -/
theorem localWitness_table {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (index : Fin 59) :
    (localWitness witness).tables[index.val]'(by
      rw [← (localWitness witness).same_length]
      change index.val < (LocalCore.tables (p := p) image source).length
      rw [LocalCore.tables_length]; exact index.isLt) =
      (witness.tables[index.val]'(by
        rw [← witness.same_length]; change index.val < (tables image source).length
        rw [tables_length]; omega)).withComponent
        ((LocalCore.tables image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt))
        (by rw [← witness.same_circuits]; exact (component_layout image source index).1)
        (by rw [← witness.same_circuits]; exact (component_layout image source index).2.1) := by
  rw [localWitness, witness.projectPrefix_getElem (index := ⟨index.val, by
    change index.val < (LocalCore.tables (p := p) image source).length
    rw [LocalCore.tables_length]; exact index.isLt⟩)]
  rw [Table.ext_iff]
  refine ⟨rfl, ?_⟩
  apply Table.projectPrefix_rows_of_width_eq
  rw [← witness.same_circuits]
  exact (component_layout image source index).1

/-- Retained table keys and absent keys have exactly the original canonical data. -/
theorem localWitness_data {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (name : String)
    (different : name ≠ "sp1.native.write_permission") (arity : ℕ) :
    (localWitness witness).data name arity = witness.data name arity := by
  apply witness.projectPrefix_data_of_layout (projectionLength image source)
    (fun index => (projectionWidth image source index).le) (projectionFixed image source)
    (projectionWidth image source)
  · intro index
    exact (component_layout image source ⟨index.val, by
      simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).2.2.1
  · intro index
    exact (component_layout image source ⟨index.val, by
      simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).2.2.2
  · intro component member
    change component ∈ (tables image source).drop (LocalCore.tables image source).length at member
    rw [LocalCore.tables_length] at member
    have length : ((((LocalCore.tables (p := p) image source).set 25 { circuit := ProtectedStore.byte }).set 26
        { circuit := ProtectedStore.half }).set 27 { circuit := ProtectedStore.word }
        |>.set 28 { circuit := ProtectedStore.double }).length = 59 := by
      simp only [List.length_set, LocalCore.tables_length]
    rw [tables, List.drop_left' length] at member
    obtain rfl := List.mem_singleton.mp member
    exact different.symm

private theorem lookup_ne_permission (image : ProgramImage) (source : ExecutionSnapshot)
    (index : Fin 59) :
    ∀ lookup ∈ ((LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact index.isLt)).operations.lookups,
      lookup.table.name ≠ "sp1.native.write_permission" := by
  intro lookup member same
  have key := LocalCore.lookup_names_subset image source _ (List.getElem_mem _) (List.mem_map_of_mem member)
  rw [same] at key
  simp at key

theorem localWitness_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) : (localWitness witness).Constraints := by
  apply witness.projectPrefix_constraints_of (target := LocalCore.ensemble image source)
    (projectionLength image source) _ _ ?_ constraints
  intro index row rowWidth checked
  rw [projectionWidth, ← rowWidth, Array.extract_size]
  have bound : index.val < 59 := by
    simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)
  have projection := component_projection (p := p) image source ⟨index.val, bound⟩
  change (tables (p := p) image source)[index.val]'(by rw [tables_length]; omega) |>.operations.ConstraintsHold
    (Environment.fromArray row witness.data) at checked
  have original : ((LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact bound)).operations.ConstraintsHold
      (Environment.fromArray row witness.data) := by
    simpa only [Operations.ConstraintsHold, projection.1, projection.2.1] using checked
  apply Operations.constraintsHold_congr_of_data_agree
    (env := Environment.fromArray row witness.data)
    (env' := Environment.fromArray row (localWitness witness).data) rfl ?_ original
  intro lookup member
  exact (localWitness_data witness lookup.table.name
    (lookup_ne_permission image source ⟨index.val, bound⟩ lookup member) lookup.table.arity).symm

private theorem provider_suffix_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (channel : RawChannel (ZMod p)) (different : channel ≠ WritePermissionProvider.channel.toRaw) :
    (witness.tables.drop 59).flatMap (·.interactionsWith witness.data channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_drop, witness.tables_map_component] at mapped
  change table.component ∈ (tables image source).drop 59 at mapped
  have length : ((((LocalCore.tables (p := p) image source).set 25 { circuit := ProtectedStore.byte }).set 26
      { circuit := ProtectedStore.half }).set 27 { circuit := ProtectedStore.word } |>.set 28 { circuit := ProtectedStore.double }).length = 59 := by
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
  apply witness.projectPrefix_interactions (target := LocalCore.ensemble image source)
    (projectionLength image source) _ _ rfl channel ?_ ?_
  · intro index row rowWidth
    rw [projectionWidth, ← rowWidth, Array.extract_size]
    have projection := (component_projection (p := p) image source ⟨index.val, by
      simpa only [LocalCore.tables_length] using (show index.val < (LocalCore.tables (p := p) image source).length from index.isLt)⟩).2.2 channel different
    change ((ensemble image source).tables[index.val]'(by have := projectionLength (p := p) image source; omega)).operations.interactionsWith channel =
      (LocalCore.ensemble image source).tables[index.val].operations.interactionsWith channel at projection
    rw [Operations.interactionValuesWith, Operations.interactionValuesWith, projection]
    exact List.map_congr_left fun interaction _ => AbstractInteraction.eval_congr rfl
  · change (witness.tables.drop (LocalCore.tables image source).length).flatMap _ = []
    rw [LocalCore.tables_length]
    exact provider_suffix_silent witness channel different

theorem old_channel_ne_permission {image : ProgramImage} {source : ExecutionSnapshot}
    (channel : RawChannel (ZMod p)) (member : channel ∈ (LocalCore.ensemble image source).channels) :
    channel ≠ WritePermissionProvider.channel.toRaw := by
  change channel ∈ (LocalCore.baseEnsemble image source).channels ++ [LocalCore.sourceChannel image source] at member
  rcases List.mem_append.mp member with member | member
  · intro same
    have names := List.mem_map_of_mem (f := RawChannel.name) member
    rw [same] at names
    simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      WritePermissionProvider.channel, stateChannel, memoryChannel, byteChannel, programChannel,
      exitChannel, syscallChannel, publicValuesChannel, Channel.toRaw] at names
  · obtain rfl := List.mem_singleton.mp member
    intro same
    have names := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList.head?) same
    dsimp only [LocalCore.sourceChannel, PublicVerifier.channel, VerifierChannel.channel,
      Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName] at names
    rw [String.toList_append] at names
    simp [LocalSourceBoundary.checker, WritePermissionProvider.channel] at names

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
