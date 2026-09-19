import SP1Clean.Soundness.CoreMemoryBalance
import SP1Clean.Soundness.LocalCoreFinalBoundary
import SP1Clean.Soundness.LocalCoreSourceGrounding

/-! # Actual Memory balance of a local shard with a complete source

The authenticated local source and canonical final inventories delimit the complete physical Memory
ledger. The interior retains ordinary instructions, refreshes, HALT, and active syscall rows.
Constraints force unit signed multiplicities; count-bounded Clean balance then gives an exact
per-location equation with unique authenticated boundary records. No Memory guarantee or
execution-order premise is used to establish this equation.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The unchanged physical Memory ledger after the two three-table inventories. -/
noncomputable def memoryInterior {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : List (TypedInteraction (memoryChannel (p := p))) :=
  (witness.tables.drop 6).flatMap (typedTableInteractionsWith · memoryChannel)

/-- The interior adapter preserves every raw interaction, including disabled interactions. -/
theorem memoryInterior_raw {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (memoryInterior witness).map TypedInteraction.raw =
      (witness.tables.drop 6).flatMap (·.interactionsWith memoryChannel.toRaw) := by
  simp only [memoryInterior, List.map_flatMap, typedTableInteractionsWith_raw]

private theorem verifier_memory_silent (image : ProgramImage) (source : ExecutionSnapshot) :
    memoryChannel.toRaw ∉ (verifier (p := p) image source).channels := by
  change memoryChannel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
  simp [OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
    stateChannel, memoryChannel, byteChannel, exitChannel, Channel.toRaw]

/-- Exact decomposition of the physical ledger into initial records, final records, and all
remaining interactions. The typed `pushedIfValue (-1)` is the finalizer's negative emission with
`assumeGuarantees = false`; signed message selection places it on the consumed side. -/
theorem memory_interactions {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    typedEnsembleInteractionsWith witness memoryChannel =
      ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel 1) ++
      (FinalMemoryEnsemble.records (finalWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel (-1)) ++
      memoryInterior witness := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedEnsembleInteractionsWith_raw, List.map_append, List.map_append, memoryInterior_raw]
  simp only [List.map_map]
  change witness.interactionsWith memoryChannel.toRaw =
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).map memoryChannel.pushedValue ++
    (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) ++ _
  rw [← source_memory_interactions witness, ← final_memory_interactions witness]
  change witness.verifierTable.interactionsWith memoryChannel.toRaw ++
    witness.tables.flatMap (·.interactionsWith memoryChannel.toRaw) = _
  rw [witness.verifierTable.interactionsWith_nil_of_channel_not_mem (verifier_memory_silent image source),
    List.nil_append]
  have split := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith memoryChannel.toRaw))
    (List.take_append_drop 3 witness.tables)
  have splitTail := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith memoryChannel.toRaw))
    (List.take_append_drop 3 (witness.tables.drop 3))
  simp only [List.flatMap_append, List.drop_drop] at split splitTail
  rw [← split, ← splitTail, List.append_assoc]
  rfl

/-- Every interaction of the unchanged interior has signed-unit multiplicity or zero. -/
theorem memoryInterior_signedBinary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints) :
    ∀ interaction ∈ memoryInterior witness,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  have rawMem := List.mem_map_of_mem (f := TypedInteraction.raw) member
  rw [memoryInterior_raw] at rawMem
  obtain ⟨table, tableMem, rowMem⟩ := List.mem_flatMap.mp rawMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp rowMem
  have componentMem := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) tableMem
  rw [List.map_drop, witness.tables_map_component] at componentMem
  change table.component ∈ NativeCore.afterFinalTables image at componentMem
  exact NativeCore.interior_memoryBinary image table.component componentMem table.data physical
    (constraints table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop tableMem))
      physical physicalMem) interaction.raw emitted

/-- Raw constraints force signed-unit multiplicities throughout the combined Memory ledger.
This includes both inventories and all active system rows. -/
theorem memory_signedBinary {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  rw [memory_interactions]
  exact NativeCore.memoryBoundary_signedBinary _ _ _ (memoryInterior_signedBinary witness constraints)

/-- Initial records and all interior pushes are a permutation of final records and all interior
pulls, as complete typed messages. Values, locations, and timestamps are preserved together. -/
theorem memory_records_perm {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness) ++ producedMessages (memoryInterior witness)).Perm
      (FinalMemoryEnsemble.records (finalWitness witness) ++ consumedMessages (memoryInterior witness)) := by
  apply NativeCore.memoryBoundary_records_perm _ _ _ (memoryInterior_signedBinary witness constraints)
  rw [← memory_interactions, typedEnsembleInteractionsWith_raw]
  exact balanced _ (by simp [ensemble, sp1Ensemble_channels])

/-- The unique final record at each finalized location, without assuming its value is current. -/
noncomputable def memoryFinalFrontier {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((FinalMemoryEnsemble.records (finalWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- The exact per-location Memory equation needed for timed grounding. Its endpoints are unique
records derived from this assembly's own ordering constraints and balance. No boundary uniqueness,
Memory truth, padding inactivity, or syscall inactivity is assumed. -/
theorem memory_frontier_balance {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(producedMessages (memoryInterior witness)) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(consumedMessages (memoryInterior witness)) : Multiset _) := by
  exact NativeCore.memoryBoundary_frontier_balance _ _ _ _
    (source_records_locations_nodup witness constraints balanced)
    (final_records_locations_nodup witness constraints balanced)
    (memory_records_perm witness constraints balanced) loc

/-- A present final frontier record has the requested canonical location. Currency of its value
and validity of its clock are conclusions still to be supplied by the timed walk. -/
theorem memoryFinalFrontier_canonical {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryFinalFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.CanonicalSpec message := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  exact ⟨of_decide_eq_true member.2, final_records_canonical witness constraints balanced _ member.1⟩

end SP1Clean.Soundness.LocalCore
