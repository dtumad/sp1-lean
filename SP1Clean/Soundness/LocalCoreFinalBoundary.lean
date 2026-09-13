import SP1Clean.Soundness.LocalCoreBoundaries
import SP1Clean.Soundness.NativeCoreFinalBoundary

/-! # Structural finalization from the local-shard AIR

The final inventory consumes Memory records without assuming their values or clocks are valid.
Its canonical addresses and unique locations follow from this assembly's own Byte closure and
private ordering ledger. The source prefix and public verifier are projected without changing rows.
These are the boundary facts needed before timed Memory grounding can establish currency.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A view of the unchanged physical suffix, with the final inventory's fixed verifier.
The omitted initialization tables are silent on the final ordering channel. -/
def finalWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble (p := p) (NativeCore.afterFinalTables image) []) :=
  EnsembleWitness.ofTables _ (witness.tables.drop 3) witness.data () (by
    rw [List.map_drop, witness.tables_map_component]
    change (tables image source).drop 3 = _
    rw [tables]
    have length : ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component)).length = 3 := rfl
    rw [List.drop_left' length, NativeCore.afterInitialTables_eq]
    rfl) (by
      intro table member
      exact witness.same_data table (List.mem_of_mem_drop member))

/-- Finalizer contracts follow before any Memory guarantees or execution facts are available. -/
theorem finalTables_spec {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
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
  have byte := (finishedChannel_guarantees image source witness constraints balanced table tableMem).1 row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte checked ⊢
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
  exact FinalMemoryEnsemble.view_spec id _ checked byte

/-- Every consumed final record has a canonical location, independently of its value and clock. -/
theorem final_records_canonical {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ FinalMemoryEnsemble.records (finalWitness witness), MemoryBoundary.CanonicalSpec record :=
  FinalMemoryEnsemble.inventory.records_valid_of_tables (finalWitness witness)
    (finalTables_spec witness constraints balanced)

private theorem sourceTables_final_silent {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take 3).flatMap
      (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  change table.component ∈ (tables image source).take 3 at mapped
  have length : ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component)).length = 3 := rfl
  rw [tables, List.take_left' length] at mapped
  obtain ⟨view, member, same⟩ := List.mem_map.mp mapped
  rw [← same]
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  have allowed := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id
  intro used
  simpa [OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
    memoryChannel, byteChannel, Channel.toRaw] using allowed used

/-- The actual local verifier fixes both endpoints of the final inventory's ordering chain. -/
theorem verifier_final_interactions (image : ProgramImage) (source : ExecutionSnapshot)
    (env : Environment (ZMod p)) :
    (⟨verifier image source⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw env =
      [(OrderedBoundary.channel OrderedFinalProvider.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel OrderedFinalProvider.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have stateEmpty (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil sp1StateVerifier.base
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw input offset (by
        simp [sp1StateVerifier, circuit_norm, OrderedBoundary.channel, OrderedFinalProvider.channelName,
          stateChannel, byteChannel, exitChannel])
  have initialEmpty (offset : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundaryVerifier.circuit (p := p) SnapshotMemoryEnsemble.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).base
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw () offset (by
      change (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉
        [(OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw]
      simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, SnapshotMemoryEnsemble.channelName, Channel.toRaw])
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
theorem finalWitness_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (finalWitness witness).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
  have suffix : witness.tables.flatMap
      (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) =
      (witness.tables.drop 3).flatMap
        (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) := by
    conv_lhs => rw [← List.take_append_drop 3 witness.tables]
    rw [List.flatMap_append, sourceTables_final_silent, List.nil_append]
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons]
  rw [suffix]
  apply congrArg (fun front => front ++ (witness.tables.drop 3).flatMap
    (·.interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw))
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_environment, EnsembleWitness.verifierTable_component]
  change (FinalMemoryEnsemble.ensemble (p := p) (NativeCore.afterFinalTables image) []).verifierTable.operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw _ =
    (⟨verifier image source⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw _
  rw [verifier_final_interactions]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
    Ensemble.verifierTable, FinalMemoryEnsemble.ensemble, OrderedMemoryEnsemble.Inventory.ensemble,
    OrderedBoundaryEnsemble.ensemble, OrderedBoundaryVerifier.circuit]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- The final inventory has one record per decoded location before any value is grounded.
This includes uniqueness across the register/RAM split and across duplicate physical rows. -/
theorem final_records_locations_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((FinalMemoryEnsemble.records (finalWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply FinalMemoryEnsemble.inventory.records_locations_nodup_of_tables
    (finalWitness witness) (NativeCore.afterFinalTables_silent image) (finalTables_spec witness constraints balanced)
  change BalancedInteractions ((finalWitness witness).interactionsWith _)
  rw [finalWitness_interactions]
  exact balanced _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The final inventory is precisely the negative Memory ledger of its three physical tables. -/
theorem final_memory_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    ((witness.tables.drop 3).take 3).flatMap (·.interactionsWith memoryChannel.toRaw) =
      (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) :=
  FinalMemoryEnsemble.memory_interactions_eq (finalWitness witness)

end SP1Clean.Soundness.LocalCore
