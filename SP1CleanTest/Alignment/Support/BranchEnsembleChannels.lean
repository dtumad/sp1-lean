import SP1CleanTest.Alignment.Support.BranchEnsembleFixture

/-! # Exact channel inventory for the branch ensemble

The registry transport retains complete raw channel identities and every physical occurrence.
-/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- The complete unique inventory of typed channels in this host assembly. -/
def channels : List (RawChannel Fp) :=
  [HostCallChip.channel.toRaw, WritePermissionProvider.channel.toRaw,
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
    stateChannel.toRaw, byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
    exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw,
    HintReadWordChip.stateChannel.toRaw, HostHintQueue.wordChannel.toRaw,
    HostHintQueue.nodeChannel.toRaw, HostHintQueue.stateChannel.toRaw, HostExitBoundary.channel.toRaw,
    (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw,
    HostRamAccessChip.channel.toRaw, (FinalMemoryValue.channel false).toRaw,
    FinalMemoryChange.channel.toRaw, (FinalMemoryValue.channel true).toRaw]

/-- The original assembly before adding the target-dependent change verifier. -/
def baseAssembly (target : MemorySnapshot) :=
  HostFinalMemory.withReceipts (p := SP1Prime) image source target
    (HostHintQueueBoundary.initial []) source.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources []) []

/-- Registry occurrence indices before the change verifier, checked by full raw records. -/
def channelOccurrences : List (Fin 22) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11, 5, 0, 0, 15, 0, 0, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 16, 0, 16, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 5, 5, 0, 17, 0, 17, 10, 13, 0, 14, 0, 14, 13, 0, 14, 0, 14, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 13, 12, 16, 16, 17, 17, 19, 19, 20, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 21, 21, 20, 14, 16, 17, 15, 14, 16, 17, 15, 19, 21]

/-- The original registration list repeats precisely these full raw channels. -/
theorem channel_expansion (target : MemorySnapshot) :
    (baseAssembly target).channels = channelOccurrences.map (fun index => channels[index.val]'(by
      change index.val < 22
      exact index.isLt)) := by
  repeat' first
    | apply congrArg₂ (@List.cons (RawChannel Fp))
    | rfl

/-- Every canonical channel has an original registration. -/
theorem channelOccurrences_complete (index : Fin 22) : index ∈ channelOccurrences := by
  fin_cases index <;> decide

/-- Equality of raw membership includes each channel's arity and predicate, not just its name. -/
private theorem base_channels_membership (target : MemorySnapshot) (channel : RawChannel Fp) :
    channel ∈ channels ↔ channel ∈ (baseAssembly target).channels := by
  rw [channel_expansion]
  constructor
  · intro member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have small : index < 22 := bound
    apply List.mem_map.mpr
    exact ⟨⟨index, small⟩, channelOccurrences_complete _, equal⟩
  · intro member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact List.getElem_mem _

/-- Export view with the same tables and public verifier and a unique channel registry. -/
def exportAssembly (target : MemorySnapshot) := (assembly target).withChannels channels



/-- Exact declared channel indices for the installed physical tables; the head records the base verifier. -/
def componentChannelIndices : List (List (Fin 22)) :=
  [[4, 5, 8, 2, 3, 14, 16, 17, 15, 14, 16, 17, 15], [5, 2, 5, 5, 5, 5, 7, 2], [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 2, 5, 5, 5, 5, 7, 2], [5, 2, 2], [5, 3, 5, 5, 5, 5, 7, 3, 19], [5, 5, 3, 5, 5, 5, 5, 7, 3, 21], [5, 3, 3], [6], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 7], [5, 4, 6, 7, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 5, 4, 5, 6, 7, 5, 5, 5, 7], [5, 4, 5, 5, 5, 5, 5, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 5, 5, 1, 4, 7], [5, 4, 6, 7, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5, 7, 7], [5, 4], [5, 4, 6, 7, 8, 7], [5, 4, 6, 7, 8, 9, 10, 5, 7, 7, 0], [1], [5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11], [5, 0, 0, 15], [0, 0], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 16, 0, 16, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [5, 5, 0, 17, 0, 17, 10], [13, 0, 14, 0, 14, 13], [0, 14, 0, 14], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [13], [12], [16, 16], [17, 17], [19, 19, 20], [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 21, 21, 20]]

private theorem change_channels_membership (keys : List (FinalMemoryChange.Key Fp))
    (channel : RawChannel Fp) :
    channel ∈ (FinalMemoryChangeBoundary.circuit keys).channels ↔
      channel = FinalMemoryChange.channel.toRaw := by
  simp only [FinalMemoryChangeBoundary.circuit, circuit_norm,
    List.mem_append, List.mem_ofFn, List.mem_singleton]
  constructor
  · rintro (⟨_, rfl⟩ | rfl) <;> rfl
  · intro same
    exact Or.inr same

/-- The dynamic change inventory adds only repeated registrations of the same full raw channel. -/
theorem channels_membership (target : MemorySnapshot) (channel : RawChannel Fp) :
    channel ∈ channels ↔ channel ∈ (assembly target).channels := by
  change channel ∈ channels ↔ channel ∈ (baseAssembly target).channels ++
    (FinalMemoryChangeBoundary.circuit ((source.sail.memorySnapshot.changes target).map
      FinalMemoryChange.encode)).channels
  rw [List.mem_append, change_channels_membership, ← base_channels_membership]
  constructor
  · exact Or.inl
  · rintro (member | rfl)
    · exact member
    · simp [channels]

private theorem verifier_channels_membership (closed : ClosedVerifier Fp)
    (ensemble : Ensemble Fp SP1PublicIO) (channel : RawChannel Fp) :
    channel ∈ (closed.verifier ensemble).channels ↔
      channel ∈ ensemble.verifier.channels ∨ channel ∈ closed.circuit.channels := by
  simp only [ClosedVerifier.verifier, circuit_norm, List.mem_append]
  tauto

private theorem base_verifier_channels (target : MemorySnapshot) :
    (baseAssembly target).verifier.channels =
      (componentChannelIndices[0]'(by decide)).map (fun index =>
        channels[index.val]'(by change index.val < 22; exact index.isLt)) := by
  repeat' first
    | apply congrArg₂ (@List.cons (RawChannel Fp))
    | rfl

/-- Every physical table retains its exact full declared channels, including empty tables. -/
theorem table_channels (target : MemorySnapshot) :
    (assembly target).tables.map (fun component => component.circuit.channels) =
      componentChannelIndices.tail.map (fun indices => indices.map (fun index =>
        channels[index.val]'(by change index.val < 22; exact index.isLt))) := by
  repeat' first
    | apply congrArg₂ List.cons
    | rfl

/-- Both the dynamic verifier and every installed component use only canonical raw channels. -/
theorem component_channels_subset (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).allTables) : component.circuit.channels ⊆ channels := by
  change component ∈ (assembly target).verifierTable :: (assembly target).tables at member
  rcases List.mem_cons.mp member with rfl | member
  · intro channel used
    change channel ∈ ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).verifier
      (baseAssembly target)).channels at used
    rw [verifier_channels_membership] at used
    rcases used with used | used
    · rw [base_verifier_channels] at used
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
      exact List.getElem_mem _
    · rw [show (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).circuit =
        FinalMemoryChangeBoundary.circuit ((source.sail.memorySnapshot.changes target).map
          FinalMemoryChange.encode) from rfl, change_channels_membership] at used
      subst channel
      simp [channels]
  · have present := List.mem_map_of_mem
      (f := fun component : Component Fp => component.circuit.channels) member
    rw [table_channels] at present
    obtain ⟨indices, _, equal⟩ := List.mem_map.mp present
    rw [← equal]
    intro channel used
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
    exact List.getElem_mem _

/-- Every physical interaction has its full raw channel in the authenticated registry. -/
theorem channels_complete (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).allTables) (interaction : AbstractInteraction Fp)
    (used : interaction ∈ component.rowOperations.interactions) : interaction.channel ∈ channels := by
  apply component_channels_subset target component member
  apply component.circuit.channels_subset component.rowInputVar component.rowOffset
  exact List.mem_map_of_mem (f := fun interaction : AbstractInteraction Fp => interaction.channel) used

end SP1Clean.Audit.BranchEnsemble
