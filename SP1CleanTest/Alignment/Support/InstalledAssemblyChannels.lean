import SP1CleanTest.Alignment.Support.InstalledAssembly

/-! # Exact channel inventory for the complete installed assembly

The registry transport retains complete raw channel identities and every physical occurrence.
-/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- Original protocol channels; public assertion channels are allocated separately. -/
def originalChannels (context : Context) : List (RawChannel Fp) :=
  [HostCallChip.channel.toRaw, WritePermissionProvider.channel.toRaw,
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
    stateChannel.toRaw, byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
    exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw,
    HintReadWordChip.stateChannel.toRaw, HostHintQueue.wordChannel.toRaw,
    HostHintQueue.nodeChannel.toRaw, HostHintQueue.stateChannel.toRaw, HostExitBoundary.channel.toRaw,
    (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw,
    HostRamAccessChip.channel.toRaw, (FinalMemoryValue.channel false).toRaw,
    FinalMemoryChange.channel.toRaw, (FinalMemoryValue.channel true).toRaw,
    context.source.sail.memorySnapshot.registerTable.channel.toRaw,
    (FinalRegisterValue.membership context.target).channel.toRaw,
    (InitialMemoryLookup.membership context.source.sail.memory (2 ^ 48) "sp1.native.initial_memory").channel.toRaw,
    (InitialMemoryLookup.membership context.target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw,
    (context.image.writePermissionTable (p := SP1Prime)).channel.toRaw,
    CommitmentDeclaration.channel.toRaw]

/-- Exact declared channel indices for every installed physical table, including empty tables. -/
def componentChannelIndices : List (List (Fin 28)) :=
  [[22, 5, 2, 5, 5, 5, 5, 7, 2], [24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 2, 5, 5, 5, 5, 7, 2], [5, 2, 2], [7, 5, 3, 5, 5, 5, 5, 7, 3, 19], [5, 7, 5, 3, 5, 5, 5, 5, 7, 3, 21], [5, 3, 3], [6], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 7], [5, 4, 6, 7, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 5, 4, 5, 6, 7, 5, 5, 5, 7], [5, 4, 5, 5, 5, 5, 5, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 5, 5, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5, 7, 7], [5, 4], [5, 4, 6, 7, 8, 7], [5, 4, 6, 7, 8, 9, 10, 5, 7, 7, 0], [22], [24], [26, 1], [26], [5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11], [5, 0, 0, 15], [0, 0], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [13, 0, 14, 0, 14, 13], [0, 14, 0, 14], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [13], [12], [16, 16], [17, 17], [23, 19, 19, 20], [25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 21, 21, 20], [23], [25], [27]]

/-- Every physical table retains its exact full declared channels, including empty tables. -/
theorem table_channels (context : Context) :
    (assembly context).tables.map (fun component => component.circuit.channels) =
      componentChannelIndices.map (fun indices => indices.map (fun index =>
        (originalChannels context)[index.val]'(by change index.val < 28; exact index.isLt))) := by
  repeat' first
    | apply congrArg₂ List.cons
    | rfl
  exact FixedProgramProvider.Preprocessed.circuit_channels (p := SP1Prime) context.image

/-- Every installed physical component uses only the original protocol channels. -/
theorem component_channels_subset (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) : component.circuit.channels ⊆ originalChannels context := by
  have present := List.mem_map_of_mem
    (f := fun component : Component Fp => component.circuit.channels) member
  rw [table_channels] at present
  obtain ⟨indices, _, equal⟩ := List.mem_map.mp present
  rw [← equal]
  intro channel used
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
  exact List.getElem_mem _

end SP1CleanTest.Alignment.InstalledAssembly
