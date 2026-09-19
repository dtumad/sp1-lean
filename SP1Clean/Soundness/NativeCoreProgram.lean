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
  simp only [InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      (List.replicate 42 byteChannel.toRaw ++
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ++
        List.replicate 4 byteChannel.toRaw ++
        [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw])
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel, byteChannel, Channel.toRaw]

/-- The computed ROM is the only possible non-pull Program contributor in this assembly. -/
theorem component_program_source (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (ensemble image).allTables) :
    component = (⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)) ∨ ProgramPulls component := by
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · right
    apply programPulls_of_silent
    change programChannel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      stateChannel, programChannel, byteChannel, exitChannel, Channel.toRaw]
  · change component ∈ tables image at member
    have split : tables (p := p) image =
        ((InitialMemoryEnsemble.views image).map (·.component) ++
          FinalMemoryEnsemble.inventory.views.map (·.component)) ++ afterFinalTables image := by
      simp only [tables, afterInitialTables, afterFinalTables, List.append_assoc]
    rw [split, List.mem_append] at member
    rcases member with boundary | interior
    · exact Or.inr (boundary_programPulls image component boundary)
    · exact interior_program_source image component interior

/-- Every active Program pull in the combined AIR names a decoded instruction in the checked
image. No Program-truth premise, execution ordering, or semantic memory binding is required. -/
theorem program_pull_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.mult = -1)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) :=
  program_pull_committed_of_sources valid witness constraints
    (balanced programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]))
    (component_program_source image) message interaction member active payload

end SP1Clean.Soundness.NativeCore
