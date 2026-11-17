import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.InitialMemoryEnsemble
import SP1Clean.Soundness.FinalMemoryEnsemble
import SP1Clean.Alignment.Chips.FixedProgramProvider.Bridge
import ToClean.Air.VerifierChannel
import ToClean.Air.EnsembleBuild
import ToClean.Circuit.SubcircuitProjection

/-! # The physical core segment shared by every assembly

Every local assembly places the same components after its initialization inventory: the final
memory inventory, the fixed decoded ROM, the instruction chips and the providers other than the
legacy unauthenticated Program and memory-boundary providers. Assemblies differ only in the
initialization inventory and memberships in front of this segment.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The core components after the initialization inventory. -/
def afterInitialTables (image : ProgramImage) : List (Component (ZMod p)) :=
  FinalMemoryEnsemble.inventory.views.map (·.component) ++
    [FixedProgramProvider.Preprocessed.component image] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

/-- Components following the final inventory: the fixed ROM, the instruction chips and the
remaining providers. -/
def afterFinalTables (image : ProgramImage) : List (Component (ZMod p)) :=
  [FixedProgramProvider.Preprocessed.component image] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

theorem afterInitialTables_eq (image : ProgramImage) :
    afterInitialTables (p := p) image =
      FinalMemoryEnsemble.inventory.views.map (·.component) ++ afterFinalTables image := by
  simp only [afterInitialTables, afterFinalTables, List.append_assoc]

/-- The final inventory's only requirements are on Memory and the two ordering channels. -/
private theorem final_requirements (component : Component (ZMod p))
    (member : component ∈ FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] := by
  simp only [OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [FinalMemoryEnsemble.viewFor, FinalMemoryEnsemble.registerView, FinalMemoryEnsemble.ramView,
      OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
      OrderedMemoryProvider.circuit, Guarded.circuit, OrderedMemoryProvider.activeCircuit,
      OrderedBoundaryEnd.circuit, FinalRegisterProvider.circuit, FinalRamProvider.circuit]

/-- The shared instruction/finalizer/provider segment closes Byte and Program requirements,
independently of the source inventory and the verifier in front of it. -/
theorem afterInitialTables_finished_requirements (image : ProgramImage)
    (component : Component (ZMod p)) (member : component ∈ afterInitialTables (p := p) image)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env)
    (romRequirements : component = FixedProgramProvider.Preprocessed.component image →
      component.operations.ChannelRequirements channel env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :=
    sp1_component_finished_requirements component member channel
      (fun mem => outside (by simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢; tauto))
      env constraints
  simp only [afterInitialTables, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at member
  rcases member with ((member | rfl) | member) | member
  · exact absent (fun required => outside (List.mem_cons_of_mem _
      (final_requirements component member required)))
  · exact romRequirements rfl
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

private theorem initialChannel_not_old :
    (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName).toRaw ∉
      (sp1Ensemble (p := p)).channels := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [sp1Ensemble_channels, OrderedBoundary.channel, OrderedInitialProvider.channelName,
    stateChannel, memoryChannel, programChannel, byteChannel, exitChannel,
    syscallChannel, publicValuesChannel, Channel.toRaw_name] at names

/-- The private initialization channel is owned only by its three inventory tables and verifier. -/
theorem afterInitialTables_silent (image : ProgramImage) :
    ∀ component ∈ afterInitialTables (p := p) image,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels := by
  intro component member
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels :=
    fun used => initialChannel_not_old (sp1Ensemble_tables_channels_subset component member used)
  simp only [afterInitialTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((member | rfl) | member) | member
  · simp only [OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      intro used <;>
      have support := FinalMemoryEnsemble.view_channels_subset _ used <;>
      simp [OrderedBoundary.channel, OrderedInitialProvider.channelName,
        OrderedFinalProvider.channelName, memoryChannel, byteChannel, Channel.toRaw] at support
  · change (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName).toRaw ∉
      (FixedProgramProvider.Preprocessed.circuit (p := p) image).channels
    rw [FixedProgramProvider.Preprocessed.circuit_channels]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel, Channel.toRaw]
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

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
  have old (member : component ∈ (sp1Ensemble (p := p)).tables) :
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw ∉ component.circuit.channels :=
    fun used => finalChannel_not_old (sp1Ensemble_tables_channels_subset component member used)
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · change (OrderedBoundary.channel (p := p) OrderedFinalProvider.channelName).toRaw ∉
      (FixedProgramProvider.Preprocessed.circuit (p := p) image).channels
    rw [FixedProgramProvider.Preprocessed.circuit_channels]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel, Channel.toRaw]
  · exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_left _ member)
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (by rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem)

end SP1Clean.Soundness.NativeCore
