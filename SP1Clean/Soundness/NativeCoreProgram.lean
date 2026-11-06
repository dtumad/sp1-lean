import SP1Clean.Soundness.CoreProgramBalance

/-! # Committed instruction fetches in the authenticated native core

The fixed image table authenticates every active Program fetch. All other native components are
silent or emit gated unit pulls. Clean's actual count-bounded balance therefore authenticates each
active fetch, independently of table order and of State/Memory grounding.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem boundary_programPulls (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (InitialMemoryEnsemble.views image).map (·.component) ++
      FinalMemoryEnsemble.inventory.views.map (·.component)) : ProgramPulls component := by
  apply programPulls_of_silent
  intro used
  rcases List.mem_append.mp member with initial | final
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
    simp only [InitialMemoryEnsemble.views, List.mem_cons, List.not_mem_nil, or_false] at viewMem
    rcases viewMem with rfl | rfl | rfl
    · have support := InitialMemoryEnsemble.view_channels_subset image .registers used
      simp [programChannel, byteChannel, memoryChannel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName, InitialMemoryLookup.membership, StaticTable.channel,
        Channel.toRaw] at support
    · have support := InitialMemoryEnsemble.view_channels_subset image .ram used
      simp [programChannel, byteChannel, memoryChannel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName, InitialMemoryLookup.membership, StaticTable.channel,
        Channel.toRaw] at support
    · have support := InitialMemoryEnsemble.view_channels_subset image .terminal used
      simp [programChannel, byteChannel, memoryChannel, OrderedBoundary.channel,
        OrderedInitialProvider.channelName, InitialMemoryLookup.membership, StaticTable.channel,
        Channel.toRaw] at support
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
    have support := FinalMemoryEnsemble.view_channels_subset (p := p) id used
    simp [programChannel, byteChannel, memoryChannel, OrderedBoundary.channel,
      OrderedFinalProvider.channelName, Channel.toRaw] at support

/-- The computed ROM is the only possible non-pull Program contributor in this assembly. -/
theorem component_program_source (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (ensemble image).tables) :
    component = (FixedProgramProvider.Preprocessed.component image) ∨ ProgramPulls component := by
  change component ∈ tables image at member
  have split : tables (p := p) image =
      ((InitialMemoryEnsemble.views image).map (·.component) ++
        FinalMemoryEnsemble.inventory.views.map (·.component)) ++ (afterFinalTables image ++ [ramMembership image]) := by
    simp only [tables, afterInitialTables, afterFinalTables, List.append_assoc]
  rw [split, List.mem_append] at member
  rcases member with boundary | interior
  · exact Or.inr (boundary_programPulls image component boundary)
  · rcases List.mem_append.mp interior with native | fixed
    · exact interior_program_source image component native
    · obtain rfl := List.mem_singleton.mp fixed
      right
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [(InitialMemoryLookup.membership image.initialMemory (2 ^ 48)
        "sp1.native.initial_memory").channel.toRaw]
      simp [programChannel, InitialMemoryLookup.membership, StaticTable.channel, Channel.toRaw]

/-- Boot checks and boundary traffic emit no Program interactions in the actual verifier. -/
theorem verifier_program_silent (image : ProgramImage) (env : Environment (ZMod p)) :
    (ensemble image).verifierOperations.interactionValuesWith programChannel.toRaw env = [] := by
  rw [verifier_values_of_registered image env programChannel.toRaw
    (by simp [baseEnsemble, sp1Ensemble_channels])]
  change (verifierInteractions image).circuitOperations.interactionValuesWith programChannel.toRaw env = []
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations,
    Operations.interactionValuesWith, Operations.interactionsWith, verifierInteractions_interactions]
  simp [verifierMain, GeneralFormalCircuit.toSubcircuit_interactions, sp1StateVerifier,
    sp1StateVerifierMain, OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main,
    OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
    stateChannel, programChannel, byteChannel, exitChannel, circuit_norm]

/-- Every active Program pull in the combined AIR names a decoded instruction in the checked
image. No Program-truth premise, execution ordering, or semantic memory binding is required. -/
theorem program_pull_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.Pull)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) :=
  program_pull_committed_of_sources valid witness constraints
    (balanced programChannel.toRaw (by simp [ensemble, baseEnsemble, sp1Ensemble_channels]))
    (by intro data emitted member
        rw [verifier_program_silent] at member
        exact (List.not_mem_nil member).elim)
    (component_program_source image) message interaction member active payload

end SP1Clean.Soundness.NativeCore
