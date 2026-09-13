import SP1Clean.Soundness.ProtectedStorePermissions
import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.EnsembleChannels

/-! # Authenticated byte permissions in the complete protected local AIR

The component inventory is exhaustive: only the fixed writable-interval table supplies permission;
the four store wrappers emit gated pulls; source, final, instruction, system, and verifier rows
otherwise remain silent. Consequently raw constraints and the ensemble's own count-bounded balance
authenticate every active permission request, with no separate provider-validity premise.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private theorem permission_not_core : WritePermissionProvider.channel.toRaw ∉ sp1CoreChannels (p := p) := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [sp1CoreChannels, WritePermissionProvider.channel, stateChannel, memoryChannel,
    byteChannel, programChannel, exitChannel, Channel.toRaw] at names

private theorem old_component_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (LocalCore.ensemble image source).allTables) :
    WritePermissionProvider.channel.toRaw ∉ component.circuit.channels := by
  have inOld (used : WritePermissionProvider.channel.toRaw ∈ (LocalCore.ensemble (p := p) image source).channels) : False :=
    old_channel_ne_permission _ used rfl
  have core (used : WritePermissionProvider.channel.toRaw ∈ sp1CoreChannels (p := p)) : False :=
    permission_not_core used
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · change WritePermissionProvider.channel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    intro used
    have names := List.mem_map_of_mem (f := RawChannel.name) used
    simp [WritePermissionProvider.channel, stateChannel, byteChannel, exitChannel,
      OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      Channel.toRaw] at names
  · change component ∈ LocalCore.tables image source at member
    rcases List.mem_append.mp member with initial | remaining
    · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp initial
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
      intro used
      have names := List.mem_map_of_mem (f := RawChannel.name)
        (SnapshotMemoryEnsemble.view_channels_subset (p := p) source.sail.memorySnapshot id used)
      simp [WritePermissionProvider.channel, memoryChannel, byteChannel, OrderedBoundary.channel,
        SnapshotMemoryEnsemble.channelName, Channel.toRaw] at names
    · simp only [NativeCore.afterInitialTables, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at remaining
      rcases remaining with ((final | rfl) | instruction) | (before | after)
      · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp final
        obtain ⟨id, _, rfl⟩ := List.mem_map.mp viewMem
        intro used
        have names := List.mem_map_of_mem (f := RawChannel.name)
          (FinalMemoryEnsemble.view_channels_subset (p := p) id used)
        simp [WritePermissionProvider.channel, memoryChannel, byteChannel, OrderedBoundary.channel,
          OrderedFinalProvider.channelName, Channel.toRaw] at names
      · change WritePermissionProvider.channel.toRaw ∉ [programChannel.toRaw]
        intro used
        have names := List.mem_map_of_mem (f := RawChannel.name) used
        simp [WritePermissionProvider.channel, programChannel, Channel.toRaw] at names
      · exact fun used => core (sp1Tables_channels_subset component instruction used)
      all_goals
        have provider : component ∈ sp1ProviderTables (p := p) := by
          first | exact List.mem_of_mem_take before | exact List.mem_of_mem_drop after
        rcases sp1ProviderTables_channels_subset_core component provider with inside | rfl
        · exact fun used => core (inside used)
        · intro used
          apply inOld
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (syscallInstrsProvider_channels_subset used))

/-- The fixed provider is the only possible positive contributor to permission balance. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).allTables) :
    component = (⟨WritePermissionProvider.circuit image⟩ : Component (ZMod p)) ∨
      WritePermission.Pulls component := by
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · right
    apply WritePermission.pulls_of_silent
    exact old_component_silent image source _ (List.mem_cons_self ..)
  · change component ∈ tables image source at member
    rcases List.mem_append.mp member with stores | fixed
    · right
      rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
          · rcases List.mem_or_eq_of_mem_set stores with original | rfl
            · exact WritePermission.pulls_of_silent component
                (old_component_silent image source component (List.mem_cons_of_mem _ original))
            · exact WritePermission.byte_pulls
          · exact WritePermission.half_pulls
        · exact WritePermission.word_pulls
      · exact WritePermission.double_pulls
    · exact Or.inl (List.mem_singleton.mp fixed)

/-- Every active request in the actual 60-table ledger names a writable native byte address. -/
theorem permission_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (address : fields 3 (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements address).toArray) :
    WritePermissionProvider.Permitted image address :=
  WritePermission.pull_permitted_of_sources image witness constraints
    (balanced _ (List.mem_cons_self ..)) (component_permission_source image source)
    address interaction member active payload

/-- A concrete active pull in any physical row inherits its provider's byte permission. -/
theorem row_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.allTables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (gate : Expression (ZMod p)) (address : Var (fields 3) (ZMod p))
    (emitted : (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
      table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : Expression.eval (table.environment physical) gate = 1) :
    WritePermissionProvider.Permitted image (eval (table.environment physical) address) := by
  apply permission_pull_permitted witness constraints balanced _
    ((WritePermissionProvider.channel.pulledIf gate address).toRaw.eval (table.environment physical))
  · apply EnsembleWitness.mem_interactionsWith.mpr
    refine ⟨table, tableMem, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    exact List.mem_map_of_mem emitted
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue, CircuitType.eval_expr, active]
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue]

end SP1Clean.Soundness.ProtectedLocalCore
