import SP1Clean.Soundness.NativeCoreBoundaries

/-! # Structural finalization from the combined native AIR

The final inventory consumes Memory records without assuming their values or clocks are valid.
Its canonical addresses and unique locations follow from Byte closure and its private ordering
ledger. These are the boundary facts needed before timed Memory grounding can establish currency.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Components following the final inventory in the physical native assembly. -/
def afterFinalTables (image : ProgramImage) : List (Component (ZMod p)) :=
  [⟨DecodedProgramProvider.circuit image⟩] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

theorem afterInitialTables_eq (image : ProgramImage) :
    afterInitialTables (p := p) image =
      FinalMemoryEnsemble.inventory.views.map (·.component) ++ afterFinalTables image := by
  simp only [afterInitialTables, afterFinalTables, List.append_assoc]

/-- A view of the unchanged physical suffix, with the final inventory's fixed verifier.
The omitted initialization tables are silent on the final ordering channel. -/
def finalWitness {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble (p := p) (afterFinalTables image) []) :=
  EnsembleWitness.ofTables _ (witness.tables.drop 3) witness.data () (by
    rw [List.map_drop, witness.tables_map_component]
    change (tables image).drop 3 = _
    rw [tables]
    have length : ((InitialMemoryEnsemble.views (p := p) image).map (·.component)).length = 3 := rfl
    rw [List.drop_left' length, afterInitialTables_eq]
    rfl) (by
      intro table member
      exact witness.same_data table (List.mem_of_mem_drop member))

private theorem finalView_spec
    (view : TransitionView (OrderedBoundary.channel (p := p) OrderedFinalProvider.channelName))
    (member : view ∈ FinalMemoryEnsemble.inventory.views) (env : Environment (ZMod p))
    (constraints : view.component.operations.ConstraintsHold env)
    (byte : view.component.operations.ChannelGuarantees byteChannel.toRaw env) :
    view.component.Spec env := by
  have assumptions : view.component.Assumptions env := by
    simp only [OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  apply component_spec_of_byte view.component ?_ env assumptions constraints byte
  simp only [OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
    simp
  · change [byteChannel.toRaw, byteChannel.toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
    simp
  · change [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] ⊆ _
    simp

/-- Finalizer contracts follow before any Memory guarantees or execution facts are available. -/
theorem finalTables_spec {image : ProgramImage} (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (finalWitness witness).tables.take (FinalMemoryEnsemble.inventory (p := p)).views.length,
      table.Spec := by
  intro table member row rowMem
  have componentMem : table.component ∈ (FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) := by
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, (finalWitness witness).tables_map_component] at mapped
    simpa only [FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
      OrderedBoundaryEnsemble.ensemble, List.take_left', List.length_map] using mapped
  obtain ⟨view, viewMem, same⟩ := List.mem_map.mp componentMem
  have tableMem : table ∈ witness.allTables :=
    witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop (List.mem_of_mem_take member))
  have byte := (finishedChannel_guarantees image witness constraints balanced table tableMem).1 row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte checked ⊢
  exact finalView_spec view viewMem _ checked byte

/-- Every consumed final record has a canonical location, independently of its value and clock. -/
theorem final_records_canonical {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ FinalMemoryEnsemble.records (finalWitness witness), MemoryBoundary.CanonicalSpec record :=
  FinalMemoryEnsemble.inventory.records_valid_of_tables (finalWitness witness)
    (finalTables_spec witness constraints balanced)

private theorem finalChannel_not_old :
    (OrderedBoundary.channel (p := p) OrderedFinalProvider.channelName).toRaw ∉
      (sp1Ensemble (p := p)).channels := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [sp1Ensemble_channels, OrderedBoundary.channel, OrderedFinalProvider.channelName,
    stateChannel, memoryChannel, programChannel, byteChannel, exitChannel,
    syscallChannel, publicValuesChannel, Channel.toRaw_name] at names

theorem afterFinalTables_silent (image : ProgramImage) :
    ∀ component ∈ afterFinalTables (p := p) image,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  have old (member : component ∈ (sp1Ensemble (p := p)).allTables) :
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels :=
    fun used => finalChannel_not_old (sp1Ensemble_allTables_channels_subset component member used)
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ [programChannel.toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel, Channel.toRaw]
  · exact old (Ensemble.mem_allTables_of_mem_tables (by
      rw [sp1Ensemble_tables]; exact List.mem_append_left _ member))
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (Ensemble.mem_allTables_of_mem_tables (by
      rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem))

private theorem initialTables_final_silent {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (witness.tables.take 3).flatMap
      (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  change table.component ∈ (tables image).take 3 at mapped
  have length : ((InitialMemoryEnsemble.views (p := p) image).map (·.component)).length = 3 := rfl
  rw [tables, List.take_left' length] at mapped
  obtain ⟨view, member, same⟩ := List.mem_map.mp mapped
  rw [← same]
  simp only [InitialMemoryEnsemble.views, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      memoryChannel, byteChannel, Channel.toRaw]
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      (List.replicate 42 byteChannel.toRaw ++
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ++
        List.replicate 4 byteChannel.toRaw ++
        [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw])
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      memoryChannel, byteChannel, Channel.toRaw]
  · change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      byteChannel, Channel.toRaw]

private theorem verifier_final_interactions (image : ProgramImage) (env : Environment (ZMod p)) :
    (⟨verifier image⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw env =
      [(OrderedBoundary.channel OrderedFinalProvider.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel OrderedFinalProvider.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have stateEmpty (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil sp1StateVerifier.base
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw input offset (by
        exact fun used => finalChannel_not_old
          (sp1Ensemble_allTables_channels_subset _ Ensemble.mem_allTables_verifierTable used))
  have initialEmpty (offset : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundaryVerifier.circuit (p := p) OrderedInitialProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).base
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw () offset (by
      change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
      simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, OrderedInitialProvider.channelName, Channel.toRaw])
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, verifier, verifierMain, circuit_norm]
  simp only [Operations.interactionsWith, OrderedBoundaryVerifier.circuit] at initialEmpty
  simp only [Operations.interactionsWith] at stateEmpty
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, stateEmpty, initialEmpty,
    List.nil_append, OrderedBoundaryVerifier.circuit]
  have final (offset : ℕ) := OrderedBoundaryVerifier.main_interactions (p := p) OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey () offset
  simp only [Operations.interactionsWith] at final
  rw [final]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]
  rfl

/-- The final proof view preserves the actual private-channel ledger, including its verifier. -/
theorem finalWitness_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (finalWitness witness).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
  have suffix : witness.tables.flatMap
      (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) := by
    conv_lhs => rw [← List.take_append_drop 3 witness.tables]
    rw [List.flatMap_append, initialTables_final_silent, List.nil_append]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons]
  rw [suffix]
  apply congrArg (fun front => front ++ (witness.tables.drop 3).flatMap
    (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw))
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_environment, EnsembleWitness.verifierTable_component]
  change (FinalMemoryEnsemble.ensemble (p := p) (afterFinalTables image) []).verifierTable.operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw _ =
    (⟨verifier image⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw _
  rw [verifier_final_interactions]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
    Ensemble.verifierTable, FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
    OrderedBoundaryEnsemble.ensemble, OrderedBoundaryVerifier.circuit]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- The final inventory has one record per decoded location before any value is grounded.
This includes uniqueness across the register/RAM split and across duplicate physical rows. -/
theorem final_records_locations_nodup {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((FinalMemoryEnsemble.records (finalWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply FinalMemoryEnsemble.inventory.records_locations_nodup_of_tables
    (finalWitness witness) (afterFinalTables_silent image) (finalTables_spec witness constraints balanced)
  change BalancedInteractions ((finalWitness witness).interactionsWith _)
  rw [finalWitness_interactions]
  exact balanced _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The final inventory is precisely the negative Memory ledger of its three physical tables. -/
theorem final_memory_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith memoryChannel.toRaw) =
      (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) :=
  FinalMemoryEnsemble.memory_interactions_eq (finalWitness witness)

end SP1Clean.Soundness.NativeCore
