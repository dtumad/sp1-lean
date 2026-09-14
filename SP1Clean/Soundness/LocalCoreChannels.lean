import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.EnsembleChannels

/-! # Complete channel inventory of the local assembly

Every verifier, source, final, instruction, and system component speaks only on a declared
local channel. Extensions can therefore prove silence on a new private channel uniformly,
without repeating the table inventory for each host protocol.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Model.Core Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The physical local component inventory is closed over its declared channels. -/
theorem component_channels_subset (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).allTables) :
    component.circuit.channels ⊆ (ensemble image source).channels := by
  have core : sp1CoreChannels (p := p) ⊆ (ensemble image source).channels := by
    intro channel used
    simp only [sp1CoreChannels, List.mem_cons, List.not_mem_nil, or_false] at used
    simp only [ensemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · change [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] ⊆ _
    intro channel used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at used
    simp only [ensemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · change component ∈ tables image source at member
    rcases List.mem_append.mp member with initial | remaining
    · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
      intro channel used
      have inside := SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id used
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      simp only [ensemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · simp only [NativeCore.afterInitialTables, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at remaining
      rcases remaining with ((final | rfl) | instruction) | (before | after)
      · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
        obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
        intro channel used
        have inside := FinalMemoryEnsemble.view_channels_subset (p := p) id used
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        simp only [ensemble, sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · intro channel used
        change channel ∈ [programChannel.toRaw] at used
        rw [List.mem_singleton] at used
        subst channel
        simp [ensemble, sp1Ensemble_channels]
      · exact fun _ used => core (sp1Tables_channels_subset component instruction used)
      all_goals
        have provider : component ∈ sp1ProviderTables (p := p) := by
          first | exact List.mem_of_mem_take before | exact List.mem_of_mem_drop after
        rcases sp1ProviderTables_channels_subset_core component provider with inside | rfl
        · exact fun _ used => core (inside used)
        · intro channel used
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (syscallInstrsProvider_channels_subset used))

end SP1Clean.Soundness.LocalCore
