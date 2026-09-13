import SP1Clean.Soundness.LocalCoreBoundaries
import SP1Clean.Soundness.CoreProgramBalance

/-! # Committed Program fetches in local shards

Source and final providers cannot contribute to Program balance. The common execution suffix has
one possible producer, the fixed decoded image. Count-bounded balance therefore authenticates
all active ordinary, HALT, and syscall fetches independently of execution ordering and host effects.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The fixed image is the only Program producer, including across both local boundaries. -/
theorem component_program_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).allTables) :
    component = (⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)) ∨ NativeCore.ProgramPulls component := by
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · right
    apply NativeCore.programPulls_of_silent
    change programChannel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      stateChannel, programChannel, byteChannel, exitChannel, Channel.toRaw]
  · change component ∈ tables image source at member
    have split : tables (p := p) image source =
        (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component) ++
          FinalMemoryEnsemble.inventory.views.map (·.component) ++ NativeCore.afterFinalTables image := by
      simp only [tables, NativeCore.afterInitialTables, NativeCore.afterFinalTables, List.append_assoc]
    rw [split, List.mem_append, List.mem_append] at member
    rcases member with (initial | final) | interior
    · right
      apply NativeCore.programPulls_of_silent
      obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
      intro used
      have subset := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id used
      simp only [List.mem_cons, List.not_mem_nil, or_false, programChannel_eq_byteChannel_false,
        programChannel_eq_memoryChannel_false, false_or] at subset
      exact (by decide : "SP1Program" ≠ SnapshotMemoryEnsemble.channelName) (congrArg RawChannel.name subset)
    · right
      apply NativeCore.programPulls_of_silent
      obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
      intro used
      have subset := FinalMemoryEnsemble.view_channels_subset (p := p) id used
      simp only [List.mem_cons, List.not_mem_nil, or_false, programChannel_eq_byteChannel_false,
        programChannel_eq_memoryChannel_false, false_or] at subset
      exact (by decide : "SP1Program" ≠ OrderedFinalProvider.channelName) (congrArg RawChannel.name subset)
    · exact NativeCore.interior_program_source image component interior

/-- Every active local Program pull names an instruction in the checked image and Sail decoder.
Image validity is also derived by `public_boundary`; it only selects the program in this statement. -/
theorem program_pull_committed {image : ProgramImage} (valid : image.Valid) {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.mult = -1)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) :=
  NativeCore.program_pull_committed_of_sources valid witness constraints
    (balanced programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]))
    (component_program_source image source) message interaction member active payload

private theorem programIndex_bound {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : 6 < witness.tables.length := by
  rw [← witness.same_length]
  change 6 < (tables image source).length
  rw [tables_length]
  decide

/-- The sole Program provider in the combined assembly. -/
def programTable {image : ProgramImage} {source : ExecutionSnapshot} (witness : EnsembleWitness (ensemble (p := p) image source)) : Table (ZMod p) :=
  witness.tables[6]'(programIndex_bound witness)

theorem programTable_component {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (programTable witness).component = (⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)) :=
  (witness.same_circuits 6 (by change 6 < (tables image source).length; rw [tables_length]; decide)).symm

/-- Every physical Program row is authenticated against this image's ROM and official Sail,
including zero-multiplicity rows. No provider-validity premise is supplied. -/
theorem program_row_committed {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints)
    (row : Array (ZMod p)) (member : row ∈ (programTable witness).table) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg ((⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)).rowInput
        ((programTable witness).environment row)).toMessage) := by
  have checked := constraints (programTable witness) (witness.mem_allTables_of_mem_tables
    (List.getElem_mem (programIndex_bound witness))) row member
  rw [programTable_component witness] at checked
  exact DecodedProgramProvider.constraints_committed valid _ checked

end SP1Clean.Soundness.LocalCore
