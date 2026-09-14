import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.NativeCoreBoundaries

/-! # Source-boundary facts from the actual local-shard AIR

The proof projection retains every physical table and the common prover data. It only restricts
the verifier to the source ordering channel. Raw constraints and the assembly's own balance prove
source-value authentication, distinct locations, the exact Memory ledger, and canonical public
endpoints. No provider-specification or source-memory-truth premise is accepted by these results.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The source inventory is a proof view of the physical assembly, with no replaced rows. -/
def sourceWitness {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    EnsembleWitness ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).ensemble
      (NativeCore.afterInitialTables image) []) :=
  EnsembleWitness.ofTables _ witness.tables witness.data () witness.tables_map_component witness.same_data

theorem sourceTables_spec {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ (sourceWitness witness).tables.take (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.length,
      table.Spec := by
  intro table member row rowMem
  have componentMem : table.component ∈ (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map (·.component) := by
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, (sourceWitness witness).tables_map_component] at mapped
    simpa only [OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      List.take_left', List.length_map] using mapped
  obtain ⟨view, viewMem, same⟩ := List.mem_map.mp componentMem
  have tableMem : table ∈ witness.allTables :=
    witness.mem_allTables_of_mem_tables (List.mem_of_mem_take member)
  have byte := (finishedChannel_guarantees image source witness constraints balanced table tableMem).1 row rowMem
  have checked := constraints table tableMem row rowMem
  rw [← same] at byte checked ⊢
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
  exact SnapshotMemoryEnsemble.view_spec source.sail.memorySnapshot id _ checked byte

/-- Every physical source record authenticates its complete value against the fixed source. -/
theorem source_records_authentic {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ record ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness),
      MemoryBoundary.SnapshotSpec source.sail.memorySnapshot record :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables (sourceWitness witness)
    (sourceTables_spec witness constraints balanced)

/-- The actual local verifier has exactly the fixed source-order endpoints on this channel. -/
theorem verifier_source_interactions (image : ProgramImage) (source : ExecutionSnapshot) (env : Environment (ZMod p)) :
    (⟨verifier image source⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw env =
      [(OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pushedValue OrderedMemoryEnsemble.startKey,
       (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).pulledValue OrderedMemoryEnsemble.endKey] := by
  have stateEmpty (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil sp1StateVerifier.base
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw input offset (by
        simp [sp1StateVerifier, circuit_norm,
          OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
          stateChannel, byteChannel, exitChannel])
  have finalEmpty (offset : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundaryVerifier.circuit (p := p) OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).base
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw () offset (by
      change (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ∉
        [(OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
      simp [OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, Channel.toRaw])
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, verifier, verifierMain, circuit_norm]
  simp only [Operations.interactionsWith, OrderedBoundaryVerifier.circuit] at finalEmpty
  simp only [Operations.interactionsWith] at stateEmpty
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, stateEmpty, finalEmpty,
    List.nil_append, List.append_nil, OrderedBoundaryVerifier.circuit]
  have source (offset : ℕ) := OrderedBoundaryVerifier.main_interactions (p := p) SnapshotMemoryEnsemble.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey () offset
  simp only [Operations.interactionsWith] at source
  rw [source]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]
  rfl

theorem sourceWitness_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (sourceWitness witness).interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw =
      witness.interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons]
  apply congrArg (fun front => front ++ witness.tables.flatMap
    (·.interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw))
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_environment, EnsembleWitness.verifierTable_component]
  change ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).ensemble
    (NativeCore.afterInitialTables image) []).verifierTable.operations.interactionValuesWith
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw _ =
    (⟨verifier image source⟩ : Component (ZMod p)).operations.interactionValuesWith
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw _
  rw [verifier_source_interactions]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
    Ensemble.verifierTable, OrderedMemoryEnsemble.Inventory.ensemble,
    OrderedBoundaryEnsemble.ensemble, OrderedBoundaryVerifier.circuit]
  exact OrderedBoundaryVerifier.interactionValues _ _ _ _ _ _

/-- Distinct source locations follow from the combined AIR, including across register/RAM tables. -/
theorem source_records_locations_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map MemoryMsg.locOf).Nodup := by
  apply (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_locations_nodup_of_tables
    (sourceWitness witness) (NativeCore.afterInitialTables_silent image) (sourceTables_spec witness constraints balanced)
  change BalancedInteractions ((sourceWitness witness).interactionsWith _)
  rw [sourceWitness_interactions]
  exact balanced _ (List.mem_cons_self ..)

/-- The source tables emit exactly the decoded records, preserving every physical occurrence. -/
theorem source_memory_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take (SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.length).flatMap
        (·.interactionsWith memoryChannel.toRaw) =
      ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map memoryChannel.pushedValue :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).memory_interactions_eq (sourceWitness witness)
    memoryChannel.pushedValue (SnapshotMemoryEnsemble.recordFor_interactions source.sail.memorySnapshot)

/-- Public endpoints are canonical, the incoming token matches the full source, and its finite
program, platform, initialization, ROM, and range checks pass without caller-supplied truth. -/
theorem public_contract_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (byte : witness.verifierTable.ChannelGuarantees byteChannel.toRaw) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧
      witness.publicInput.SourceFor source ∧ witness.publicInput.PreservesStoppedClock source := by
  have spec : witness.verifierTable.Spec := by
    intro row member
    exact NativeCore.component_spec_of_byte (⟨verifier image source⟩ : Component (ZMod p)) (List.Subset.refl _) _ (by trivial)
      (constraints _ witness.mem_allTables_verifierTable row member)
      (byte row member)
  exact EnsembleWitness.verifierSpec_iff_verifierTable_spec.mpr spec

/-- The complete witness supplies the verifier's Byte guarantees. -/
theorem public_contract {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧
      witness.publicInput.SourceFor source ∧ witness.publicInput.PreservesStoppedClock source :=
  public_contract_of_byte witness constraints
    ((finishedChannel_guarantees image source witness constraints balanced _ witness.mem_allTables_verifierTable).1)

/-- Canonical public endpoints, complete source validity, and incoming-state binding. -/
theorem public_boundary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    witness.publicInput.LimbBounds ∧ ExecutionSourceValid image source ∧ witness.publicInput.SourceFor source := by
  have checked := public_contract witness constraints balanced
  exact ⟨checked.1, checked.2.1, checked.2.2.1⟩

/-- A stopped source cannot advance the natural State clock. -/
theorem stopped_clock {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (stopped : source.host.exitCode ≠ none) :
    clkNat witness.publicInput.final_clk_high witness.publicInput.final_clk_low =
      clkNat witness.publicInput.init_clk_high witness.publicInput.init_clk_low := by
  have same := (public_contract witness constraints balanced).2.2.2 stopped
  rw [same.1, same.2]

end SP1Clean.Soundness.LocalCore
