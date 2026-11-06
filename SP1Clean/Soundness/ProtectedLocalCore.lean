import SP1Clean.Soundness.LocalCoreChannels
import SP1Clean.Proofs.Chips.ProtectedStore
import SP1Clean.Native.Operations.WritePermission

/-! # Local AIR with explicit ROM write protection

Four instruction components acquire byte-permission requests. A permission row checks each address
against a verifier-fixed interval-membership provider. The complete source verifier and all other tables are retained. This is the native
assembly intended for the capstone. `ProtectedLocalCoreExecution` derives ordinary ROM preservation
from its additional ledger; active host effects and complete execution reconstruction remain open.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The four store positions in the shared instruction inventory, after the seven boundary rows. -/
def tables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  let stores := LocalCore.tables image source
    |>.set 25 { circuit := ProtectedStore.byte, generation := StoreByteChip.generation, Assumptions := (ProtectedStore.byte).Assumptions }
    |>.set 26 { circuit := ProtectedStore.half, generation := StoreHalfChip.generation, Assumptions := (ProtectedStore.half).Assumptions }
    |>.set 27 { circuit := ProtectedStore.word, generation := StoreWordChip.generation, Assumptions := (ProtectedStore.word).Assumptions }
    |>.set 28 { circuit := ProtectedStore.double, generation := StoreDoubleChip.generation, Assumptions := (ProtectedStore.double).Assumptions }
  stores ++ [WritePermissionProvider.component image,
    WritePermissionProvider.membershipComponent image]

/-- Permission wrappers keep the original stores' canonical data keys. -/
theorem tables_names (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).map (·.circuit.name) =
      (LocalCore.tables (p := p) image source).map (·.circuit.name) ++
        ["sp1.native.write_permission", "sp1.native.write_permission.provider"] := by
  unfold tables WritePermissionProvider.membershipComponent ProgramImage.writePermissionTable
  rfl

/-- The request and fixed-membership components have distinct new data keys. -/
theorem tables_unique_names (image : ProgramImage) (source : ExecutionSnapshot) :
    ((tables (p := p) image source).map (·.circuit.name)).Nodup := by
  rw [tables_names, List.nodup_append]
  refine ⟨(LocalCore.baseEnsemble image source).unique_names, by simp, ?_⟩
  simp only [LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
    SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
    MemorySnapshot.registerTable, StaticTable.ofRows]
  exact of_decide_eq_true rfl

private theorem byte_channels (channel : RawChannel (ZMod p))
    (used : channel ∈ (ProtectedStore.byte (p := p)).channels) :
    channel ∈ (sp1Ensemble (p := p)).channels ∨ channel = WritePermissionProvider.channel.toRaw := by
  have requirements : (StoreByteChip.circuit (p := p)).channelsWithRequirements =
      [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
  simp only [GeneralFormalCircuit.channels, ProtectedStore.byte, circuit_norm, requirements,
    List.mem_cons, List.not_mem_nil, or_false] at used
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem half_channels (channel : RawChannel (ZMod p))
    (used : channel ∈ (ProtectedStore.half (p := p)).channels) :
    channel ∈ (sp1Ensemble (p := p)).channels ∨ channel = WritePermissionProvider.channel.toRaw := by
  have requirements : (StoreHalfChip.circuit (p := p)).channelsWithRequirements =
      [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
  simp only [GeneralFormalCircuit.channels, ProtectedStore.half, circuit_norm, requirements,
    List.mem_cons, List.not_mem_nil, or_false] at used
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem word_channels (channel : RawChannel (ZMod p))
    (used : channel ∈ (ProtectedStore.word (p := p)).channels) :
    channel ∈ (sp1Ensemble (p := p)).channels ∨ channel = WritePermissionProvider.channel.toRaw := by
  have requirements : (StoreWordChip.circuit (p := p)).channelsWithRequirements =
      [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
  simp only [GeneralFormalCircuit.channels, ProtectedStore.word, circuit_norm, requirements,
    List.mem_cons, List.not_mem_nil, or_false] at used
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem double_channels (channel : RawChannel (ZMod p))
    (used : channel ∈ (ProtectedStore.double (p := p)).channels) :
    channel ∈ (sp1Ensemble (p := p)).channels ∨ channel = WritePermissionProvider.channel.toRaw := by
  have requirements : (StoreDoubleChip.circuit (p := p)).channelsWithRequirements =
      [Channels.stateChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
  simp only [GeneralFormalCircuit.channels, ProtectedStore.double, circuit_norm, requirements,
    List.mem_cons, List.not_mem_nil, or_false] at used
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Physical components only use the original base channels and the two permission protocols.
The public verifier's fresh assertion channel is not a physical-table requirement. -/
theorem component_channels_subset (image : ProgramImage) (source : ExecutionSnapshot)
    (table : Component (ZMod p)) (member : table ∈ tables image source) :
    table.circuit.channels ⊆ WritePermissionProvider.channel.toRaw ::
      image.writePermissionTable.channel.toRaw :: (LocalCore.baseEnsemble image source).channels := by
  intro channel used
  have old {table : Component (ZMod p)} (member : table ∈ LocalCore.tables image source)
      (used : channel ∈ table.circuit.channels) :
      channel ∈ WritePermissionProvider.channel.toRaw :: image.writePermissionTable.channel.toRaw ::
        (LocalCore.baseEnsemble image source).channels :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (LocalCore.component_channels_subset image source table member used))
  have core (member : channel ∈ (sp1Ensemble (p := p)).channels) :
      channel ∈ WritePermissionProvider.channel.toRaw :: image.writePermissionTable.channel.toRaw ::
        (LocalCore.baseEnsemble image source).channels := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  simp only [tables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with stores | rfl | rfl
  · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
          · exact old stores used
          · rcases byte_channels channel used with supported | rfl
            · exact core supported
            · exact List.mem_cons_self ..
        · rcases half_channels channel used with supported | rfl
          · exact core supported
          · exact List.mem_cons_self ..
      · rcases word_channels channel used with supported | rfl
        · exact core supported
        · exact List.mem_cons_self ..
    · rcases double_channels channel used with supported | rfl
      · exact core supported
      · exact List.mem_cons_self ..
  · change channel ∈ [image.writePermissionTable.channel.toRaw] ++
      [WritePermissionProvider.channel.toRaw] at used
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at used
    rcases used with rfl | rfl <;> simp
  · change channel ∈ [image.writePermissionTable.channel.toRaw] at used
    obtain rfl := List.mem_singleton.mp used
    simp

def ensemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source
  unique_names := tables_unique_names image source
  channels := WritePermissionProvider.channel.toRaw :: image.writePermissionTable.channel.toRaw ::
    (LocalCore.ensemble image source).channels
  verifier := (LocalCore.ensemble image source).verifier
  unique_channel_names := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ?_, (LocalCore.ensemble image source).unique_channel_names⟩
    all_goals
      simp only [LocalCore.ensemble, PublicVerifier.install, LocalCore.baseEnsemble,
        MemorySnapshot.registerTable, StaticTable.ofRows, StaticTable.channel,
        InitialMemoryLookup.membership, OrderedBoundary.channel, Channel.toRaw_name,
        SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, sp1Ensemble_channels,
        List.map_cons, List.map_append, List.map_nil, ProgramImage.writePermissionTable,
        WritePermissionProvider.channel, PublicVerifier.channel, VerifierChannel.channel,
        VerifierChannel.channelName, VerifierChannel.channelNames, Verifier.zeroChannel,
        LocalSourceBoundary.checker]
      exact of_decide_eq_true rfl
  tables_channels := by
    intro table member channel used
    have support := component_channels_subset image source table member used
    simp only [List.mem_cons] at support ⊢
    rcases support with permission | membership | core
    · exact Or.inl permission
    · exact Or.inr (Or.inl membership)
    · exact Or.inr (Or.inr (List.mem_append_left _ core))
  verifier_channels := fun _ used => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    ((LocalCore.ensemble image source).verifier_channels used))

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).length = 63 := by
  simp only [tables, List.length_append, List.length_set, List.length_cons, List.length_nil, LocalCore.tables_length]

end SP1Clean.Soundness.ProtectedLocalCore
