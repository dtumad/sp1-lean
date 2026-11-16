import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Soundness.EnsembleLookups

/-! # Lookup freedom of the local execution assembly

Decoded ROM columns and syscall-code arithmetic are fixed by the supplied image and profile.
Source register and RAM membership use fixed-column channel providers, and the native byte
providers use bit decompositions: no table of the local assembly uses a lookup. Local
constraints therefore survive canonical-data changes when physical row cells are retained.
Channel guarantees remain separate obligations, established from actual balance and fixed
prefixes.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem final_lookups (component : Component (ZMod p))
    (member : component ∈ FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.operations.lookups = [] := by
  change component ∈ [(FinalMemoryEnsemble.registerView (p := p)).component,
    (FinalMemoryEnsemble.ramView (p := p)).component,
    (OrderedMemoryEnsemble.terminalView OrderedFinalProvider.channelName (by decide)).component] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact FinalMemoryEnsemble.view_lookups .registers
  · exact FinalMemoryEnsemble.view_lookups .ram
  · exact FinalMemoryEnsemble.view_lookups .terminal

private theorem source_lookupFree (source : ExecutionSnapshot) :
    LookupFree ((SnapshotMemoryEnsemble.inventory (p := p) source.sail.memorySnapshot).views.map
      (·.component)) := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil, LookupFree.cons_iff,
    LookupFree.nil, and_true]
  refine ⟨?_, ?_, ?_⟩
  · simp only [SnapshotMemoryEnsemble.registerView, OrderedMemoryEnsemble.providerView,
      Component.lookups_eq, Component.rowOperations, OrderedMemoryProvider.circuit, Guarded.circuit]
    exact Guarded.main_lookups _ _ _ _
  · simp only [SnapshotMemoryEnsemble.ramView, OrderedMemoryEnsemble.providerView,
      Component.lookups_eq, Component.rowOperations, OrderedMemoryProvider.circuit, Guarded.circuit]
    exact Guarded.main_lookups _ _ _ _
  · simp [SnapshotMemoryEnsemble.terminalView, OrderedMemoryEnsemble.terminalView,
      Component.lookups_eq, Component.rowOperations, OrderedBoundaryEnd.circuit, circuit_norm]

/-- Fixed source/ROM membership and native providers depend on physical cells, not generation
data, so local constraints transport across canonical projections without asserting data
equality. -/
theorem tables_lookupFree (image : ProgramImage) (source : ExecutionSnapshot) :
    LookupFree (tables (p := p) image source) := by
  intro component member
  rcases List.mem_append.mp member with snapshot | rest
  · exact source_lookupFree source component snapshot
  rcases List.mem_append.mp rest with rest | fixed
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    all_goals simp [SnapshotMemoryEnsemble.registerMembership, SnapshotMemoryEnsemble.ramMembership,
      StaticTable.component, StaticTable.provider, Component.lookups_eq, Component.rowOperations,
      circuit_norm]
  rcases List.mem_append.mp rest with retained | provider
  · rcases List.mem_append.mp retained with boundary | instruction
    · rcases List.mem_append.mp boundary with final | rom
      · exact final_lookups component final
      · obtain rfl := List.mem_singleton.mp rom
        exact FixedProgramProvider.Preprocessed.component_lookups image
    · exact sp1Tables_lookups_empty component instruction
  · apply sp1Ensemble_lookupFree
    rw [sp1Ensemble_tables]
    apply List.mem_append_right
    rcases List.mem_append.mp provider with before | after
    · exact List.mem_of_mem_take before
    · exact List.mem_of_mem_drop after

end SP1Clean.Soundness.LocalCore
