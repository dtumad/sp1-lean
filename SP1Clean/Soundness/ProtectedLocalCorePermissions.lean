import SP1Clean.Soundness.ProtectedStorePermissions
import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.LocalCoreChannels

/-! # Permission sources in the protected local tables

The component inventory is exhaustive: only the fixed writable-interval table supplies permission,
the four store wrappers emit gated pulls, and every other component is silent on both permission
channels. The host assembly derives authenticated permission requests from these facts.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem old_component_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (LocalCore.ensemble image source).tables) :
    WritePermissionProvider.channel.toRaw ∉ component.circuit.channels := by
  intro used
  exact old_channel_ne_permission _
    (List.mem_append_left _ (LocalCore.component_channels_subset image source component member used)) rfl

/-- The fixed provider is the only possible positive contributor to permission balance. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component = (WritePermissionProvider.component image : Component (ZMod p)) ∨
      WritePermission.Pulls component := by
  change component ∈ tables image source at member
  rcases List.mem_append.mp member with stores | fixed
  · right
    rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with original | rfl
          · exact WritePermission.pulls_of_silent component
              (old_component_silent image source component original)
          · exact WritePermission.byte_pulls
        · exact WritePermission.half_pulls
      · exact WritePermission.word_pulls
    · exact WritePermission.double_pulls
  · rcases List.mem_cons.mp fixed with fixed | fixed
    · exact Or.inl fixed
    · right
      rw [List.mem_singleton.mp fixed]
      apply WritePermission.pulls_of_silent
      change WritePermissionProvider.channel.toRaw ∉ [image.writePermissionTable.channel.toRaw]
      simp [WritePermissionProvider.channel, StaticTable.channel, ProgramImage.writePermissionTable,
        StaticTable.ofRows, Channel.toRaw]

/-- The fixed interval table is the only component that may provide membership. -/
theorem component_membership_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component = WritePermissionProvider.membershipComponent image ∨
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
  change component ∈ tables image source at member
  rcases List.mem_append.mp member with stores | fixed
  · right
    have original (component : Component (ZMod p))
        (member : component ∈ (LocalCore.ensemble image source).tables) :
        image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
      intro used
      exact old_channel_ne_membership _ (List.mem_append_left _
        (LocalCore.component_channels_subset image source component member
          (List.mem_append_right _ used))) rfl
    rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with old | rfl
          · exact original component old
          · change (image.writePermissionTable (p := p)).channel.toRaw ∉
              [WritePermissionProvider.channel.toRaw, stateChannel.toRaw, memoryChannel.toRaw]
            simp [ProgramImage.writePermissionTable, StaticTable.ofRows, StaticTable.channel,
              stateChannel, memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
        · change (image.writePermissionTable (p := p)).channel.toRaw ∉
              [WritePermissionProvider.channel.toRaw, stateChannel.toRaw, memoryChannel.toRaw]
          simp [ProgramImage.writePermissionTable, StaticTable.ofRows, StaticTable.channel,
            stateChannel, memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
      · change (image.writePermissionTable (p := p)).channel.toRaw ∉
              [WritePermissionProvider.channel.toRaw, stateChannel.toRaw, memoryChannel.toRaw]
        simp [ProgramImage.writePermissionTable, StaticTable.ofRows, StaticTable.channel,
          stateChannel, memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
    · change (image.writePermissionTable (p := p)).channel.toRaw ∉
              [WritePermissionProvider.channel.toRaw, stateChannel.toRaw, memoryChannel.toRaw]
      simp [ProgramImage.writePermissionTable, StaticTable.ofRows, StaticTable.channel,
        stateChannel, memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
  · rcases List.mem_cons.mp fixed with fixed | fixed
    · right
      rw [fixed]
      change image.writePermissionTable.channel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
      simp [WritePermissionProvider.channel, StaticTable.channel, ProgramImage.writePermissionTable,
        StaticTable.ofRows, Channel.toRaw]
    · exact Or.inl (List.mem_singleton.mp fixed)

end SP1Clean.Soundness.ProtectedLocalCore
