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

/-- The full physical inventory and protocol registry before source assertions are installed. -/
def rawAssembly (context : Context) : Ensemble Fp SP1PublicIO :=
  let resources := HostHintReadLocal.sourceResources (p := SP1Prime) context.source.host.io.hints ++
    FinalMemoryChecks.checkTables context.target
  let auxiliary := (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
    (HostHintReadHandoff.wordResources ++ resources)
  HostLocalCore.baseEnsemble context.image context.source auxiliary
    ((HintReadWordChip.stateChannel.toRaw :: auxiliary.flatMap (·.circuit.channels)) ++ [])
    (HostFinalMemory.source_unique_names context.image context.source context.target)

/-- Source checks installed on the complete inventory, before host endpoints. -/
def beforeBoundary (context : Context) : Ensemble Fp SP1PublicIO :=
  HostHintReadLocal.ensemble context.image context.source HostCallReceivers.available
    (HostHintReadLocal.sourceResources context.source.host.io.hints ++ FinalMemoryChecks.checkTables context.target) []
    (HostFinalMemory.source_unique_names context.image context.source context.target)

/-- The original assembly before adding the target-dependent change verifier. -/
def baseAssembly (context : Context) :=
  HostFinalMemory.withReceipts (p := SP1Prime) context.image context.source context.target
    context.finalHints context.finalHost HostCallReceivers.available
    (HostHintReadLocal.sourceResources context.source.host.io.hints) [] (HostFinalMemory.source_unique_names context.image context.source context.target)

/-- Source and host assertion channels are retained alongside every protocol channel. -/
def baseChannels (context : Context) : List (RawChannel Fp) :=
  originalChannels context ++
    [(LocalSourceBoundary.checker context.image context.source).channel (rawAssembly context),
     (HostHintQueueBoundary.boundary context.source context.finalHints context.finalHost).channel
       (beforeBoundary context)]

/-- The complete unique registry includes the target-change verifier's assertion channel. -/
def withoutCommitmentChannels (context : Context) : List (RawChannel Fp) :=
  baseChannels context ++
    [(FinalMemoryChangeBoundary.closed context.source.sail.memorySnapshot context.target).channel (baseAssembly context)]

/-- The immutable statement checker is separate from every physical protocol channel. -/
def channels (context : Context) : List (RawChannel Fp) :=
  withoutCommitmentChannels context ++
    [(CommitmentBoundary.checker context.commitments).channel
      (CommitmentEnsemble.withSource context.commitments (withoutCommitments context) (declaration_fresh context))]

/-- Registry occurrence indices before the change verifier, checked by full raw records. -/
def channelOccurrences : List (Fin 30) :=
  [0, 1, 26, 2, 3, 22, 24, 4, 5, 6, 7, 8, 9, 10, 11, 5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11, 5, 0, 0, 15, 0, 0, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 16, 27, 0, 16, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 5, 5, 27, 0, 17, 27, 0, 17, 10, 13, 0, 14, 0, 14, 13, 0, 14, 0, 14, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11, 13, 12, 16, 16, 17, 17, 23, 19, 19, 20, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 21, 21, 20, 23, 25, 28, 14, 16, 17, 15, 14, 16, 17, 15, 29, 19, 21]

/-- The original registration list repeats precisely these full raw channels. -/
theorem channel_expansion (context : Context) :
    (baseAssembly context).channels = channelOccurrences.map (fun index => (baseChannels context)[index.val]'(by
      change index.val < 30
      exact index.isLt)) := by
  repeat' first
    | apply congrArg₂ (@List.cons (RawChannel Fp))
    | rfl

/-- Every canonical channel has an original registration. -/
theorem channelOccurrences_complete (index : Fin 30) : index ∈ channelOccurrences := by
  fin_cases index <;> decide

/-- Full raw membership includes each channel's arity and predicate. -/
private theorem base_channels_membership (context : Context) (channel : RawChannel Fp) :
    channel ∈ baseChannels context ↔ channel ∈ (baseAssembly context).channels := by
  rw [channel_expansion]
  constructor
  · intro member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have small : index < 30 := bound
    exact List.mem_map.mpr ⟨⟨index, small⟩, channelOccurrences_complete _, equal⟩
  · intro member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact List.getElem_mem _

/-- Exact declared channel indices for every installed physical table, including empty tables. -/
def componentChannelIndices : List (List (Fin 28)) :=
  [[22, 5, 2, 5, 5, 5, 5, 7, 2], [24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 5, 5, 24, 5, 5, 5, 2, 5, 5, 5, 5, 7, 2], [5, 2, 2], [5, 3, 5, 5, 5, 5, 7, 3, 19], [5, 5, 3, 5, 5, 5, 5, 7, 3, 21], [5, 3, 3], [6], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 7], [5, 4, 6, 7, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 5, 4, 7], [5, 5, 4, 5, 6, 7, 5, 5, 5, 7], [5, 4, 5, 5, 5, 5, 5, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 4, 7], [5, 4, 5, 5, 7, 5, 6, 7, 5, 5, 1, 4, 7], [5, 4, 6, 7, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5, 4, 6, 7, 4, 7], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5], [5, 7, 7], [5, 4], [5, 4, 6, 7, 8, 7], [5, 4, 6, 7, 8, 9, 10, 5, 7, 7, 0], [22], [24], [26, 1], [26], [5, 5, 12, 5, 5, 13, 0, 14, 11, 13, 12, 0, 14, 11], [5, 0, 0, 15], [0, 0], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 16, 27, 0, 16, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [5, 5, 27, 0, 17, 27, 0, 17, 10], [13, 0, 14, 0, 14, 13], [0, 14, 0, 14], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [5, 7, 12, 5, 5, 18, 1, 1, 1, 1, 1, 1, 1, 1, 11, 7, 18, 12, 1, 11], [13], [12], [16, 16], [17, 17], [23, 19, 19, 20], [25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 5, 5, 5, 5, 25, 5, 21, 21, 20], [23], [25], [27]]

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

/-- Registry reindexing retains every protocol and assertion channel by full raw identity. -/
theorem without_channels_membership (context : Context) (channel : RawChannel Fp) :
    channel ∈ withoutCommitmentChannels context ↔ channel ∈ (withoutCommitments context).channels := by
  change channel ∈ baseChannels context ++ [_] ↔
    channel ∈ ((baseAssembly context).channels ++
      (FinalMemoryChangeBoundary.circuit ((context.source.sail.memorySnapshot.changes context.target).map
        FinalMemoryChange.encode)).channels) ++ [_]
  simp only [List.mem_append, change_channels_membership, ← base_channels_membership]
  have registered : (FinalMemoryChange.channel (p := SP1Prime)).toRaw ∈ baseChannels context := by
    apply List.mem_append_left
    simp [originalChannels]
  constructor
  · rintro (member | member)
    · exact Or.inl (Or.inl member)
    · exact Or.inr member
  · rintro ((member | same) | member)
    · exact Or.inl member
    · exact Or.inl (same.symm ▸ registered)
    · exact Or.inr member

/-- Every physical table retains its exact full declared channels, including empty tables. -/
theorem table_channels (context : Context) :
    (assembly context).tables.map (fun component => component.circuit.channels) =
      componentChannelIndices.map (fun indices => indices.map (fun index =>
        (originalChannels context)[index.val]'(by change index.val < 28; exact index.isLt))) := by
  repeat' first
    | apply congrArg₂ List.cons
    | rfl
  exact FixedProgramProvider.Preprocessed.circuit_channels context.image

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

/-- Every physical interaction has its full raw channel in the authenticated registry. -/
theorem channels_complete (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) (interaction : AbstractInteraction Fp)
    (used : interaction ∈ component.operations.interactions) : interaction.channel ∈ channels context := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply component_channels_subset context component member
  apply component.circuit.channels_subset component.rowInputVar component.rowOffset
  rw [Component.interactions_eq] at used
  exact List.mem_map_of_mem (f := fun interaction : AbstractInteraction Fp => interaction.channel) used


/-- Distinct stems separate the four check names without evaluating the dynamic target inventory. -/
private theorem check_name_prefixes (context : Context) :
    ([(LocalSourceBoundary.checker context.image context.source).channel (rawAssembly context),
      (HostHintQueueBoundary.boundary context.source context.finalHints context.finalHost).channel
        (beforeBoundary context),
      (FinalMemoryChangeBoundary.closed context.source.sail.memorySnapshot context.target).channel (baseAssembly context),
      (CommitmentBoundary.checker context.commitments).channel
        (CommitmentEnsemble.withSource context.commitments (withoutCommitments context) (declaration_fresh context))].map
        (fun channel => channel.name.toList.take 8)) =
      ["sp1.loca".toList, "host-bou".toList, "final-me".toList, "commitme".toList] := by
  simp only [List.map_cons, List.map_nil, PublicVerifier.channel, ClosedVerifier.channel,
    VerifierChannel.channel, Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName,
    LocalSourceBoundary.checker, HostHintQueueBoundary.boundary, HostBoundary.closed,
    FinalMemoryChangeBoundary.closed, CommitmentBoundary.checker, String.toList_append]
  rfl

/-- Protocol and check channels have distinct names as well as distinct raw records. -/
theorem channels_unique (context : Context) : ((channels context).map RawChannel.name).Nodup := by
  simp only [channels, withoutCommitmentChannels, baseChannels, List.map_append, List.append_assoc, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  have prefixes := check_name_prefixes context
  simp only [List.map_cons, List.map_nil] at prefixes
  refine ⟨?_, List.Nodup.of_map (fun name : String => name.toList.take 8) ?_, ?_⟩
  · simp only [originalChannels, List.map_cons, List.map_nil, Channel.toRaw,
      StaticTable.channel, ProgramImage.writePermissionTable, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, FinalRegisterValue.membership]
    decide
  · change ([_, _, _, _].map (fun name : String => name.toList.take 8)).Nodup
    simpa only [List.map_cons, List.map_nil, prefixes] using
      (show ["sp1.loca".toList, "host-bou".toList, "final-me".toList, "commitme".toList].Nodup from by decide)
  · intro a old b added same
    have present := List.mem_map_of_mem (f := fun name : String => name.toList.take 8) added
    change b.toList.take 8 ∈ [_, _, _, _] at present
    rw [prefixes] at present
    have separate : ∀ name ∈ (originalChannels context).map RawChannel.name,
        name.toList.take 8 ∉ ["sp1.loca".toList, "host-bou".toList, "final-me".toList, "commitme".toList] := by
      simp only [originalChannels, List.map_cons, List.map_nil, Channel.toRaw,
        StaticTable.channel, ProgramImage.writePermissionTable, InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, FinalRegisterValue.membership]
      decide
    exact separate a old (same.symm ▸ present)

private theorem checkZeros_channel (name : String) (values : List (Expression Fp))
    (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (Verifier.checkZeros name values).circuitOperations.interactions) :
    interaction.channel = (Verifier.zeroChannel name).toRaw := by
  simp only [Verifier.circuitOperations, Verifier.checkZeros_operations,
    Verifier.Operations.circuitOperations_interactions, Verifier.Operations.interactions,
    List.mem_map, List.mem_flatMap] at used
  obtain ⟨operation, ⟨value, _, member⟩, rfl⟩ := used
  simp only [Verifier.checkZero, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

private theorem andThen_channels (first second : Verifier.Program Fp SP1PublicIO)
    (registry : List (RawChannel Fp))
    (left : ∀ interaction ∈ first.circuitOperations.interactions, interaction.channel ∈ registry)
    (right : ∀ interaction ∈ second.circuitOperations.interactions, interaction.channel ∈ registry) :
    ∀ interaction ∈ (first.andThen second).circuitOperations.interactions,
      interaction.channel ∈ registry := by
  intro interaction used
  simp only [Verifier.Program.andThen, Verifier.Program.circuitOperations, Verifier.Program.operations,
    Verifier.operations_bind, Verifier.Operations.circuitOperations, Verifier.Operations.interactions,
    List.map_append, Operations.interactions_append, List.mem_append] at used
  rcases used with used | used
  · exact left interaction used
  · exact right interaction used

private theorem closed_program_channels (closed : ClosedVerifier Fp) (ens : Ensemble Fp SP1PublicIO)
    (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (closed.program ens).circuitOperations.interactions) :
    interaction.channel ∈ closed.circuit.channels ∨ interaction.channel = closed.channel ens := by
  change interaction ∈ (closed.emit >>= fun _ =>
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactions at used
  simp only [Verifier.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.interactions_append, List.mem_append] at used
  rcases used with original | check
  · left
    have member : interaction ∈ closed.operations.interactions := by
      rw [← closed.emit_interactions]
      exact original
    exact closed.circuit.channels_subset () 0 (List.mem_map_of_mem (f := AbstractInteraction.channel) member)
  · exact Or.inr (checkZeros_channel _ _ interaction check)


private theorem raw_verifier_channels (context : Context) (interaction : AbstractInteraction Fp)
    (used : interaction ∈ (rawAssembly context).verifierOperations.interactions) :
    interaction.channel ∈ originalChannels context := by
  have inventory : ((rawAssembly context).verifierOperations.interactions.map (·.channel)) =
      ([4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 8, 2, 2, 3, 3] : List (Fin 28)).map
        (fun index => (originalChannels context)[index.val]'(by change index.val < 28; exact index.isLt)) := by rfl
  have member := List.mem_map_of_mem (f := AbstractInteraction.channel) used
  rw [inventory] at member
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  exact equal ▸ List.getElem_mem _

private theorem host_boundary_channels (context : Context) (channel : RawChannel Fp)
    (used : channel ∈ (HostHintQueueBoundary.boundary (p := SP1Prime) context.source
      context.finalHints context.finalHost).circuit.channels) : channel ∈ originalChannels context := by
  have inventory : (HostHintQueueBoundary.boundary (p := SP1Prime) context.source
      context.finalHints context.finalHost).circuit.channels =
      ([14, 16, 17, 15, 14, 16, 17, 15] : List (Fin 28)).map
        (fun index => (originalChannels context)[index.val]'(by change index.val < 28; exact index.isLt)) := by rfl
  rw [inventory] at used
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
  exact List.getElem_mem _

private theorem base_verifier_channels (context : Context) :
    ∀ interaction ∈ (baseAssembly context).verifierOperations.interactions,
      interaction.channel ∈ baseChannels context := by
  have sourceChannels : ∀ interaction ∈ (beforeBoundary context).verifierOperations.interactions,
      interaction.channel ∈ baseChannels context := by
    apply andThen_channels (rawAssembly context).verifier
      ((LocalSourceBoundary.checker context.image context.source).program (rawAssembly context))
    · intro interaction used
      exact List.mem_append_left _ (raw_verifier_channels context interaction used)
    · intro interaction used
      have same := checkZeros_channel
        ((LocalSourceBoundary.checker context.image context.source).channelName (rawAssembly context))
        ((LocalSourceBoundary.checker context.image context.source).assertions (varFromOffset SP1PublicIO 0)) interaction used
      rw [same]
      exact List.mem_append_right _ (List.mem_cons_self)
  apply andThen_channels (beforeBoundary context).verifier
    ((HostHintQueueBoundary.boundary context.source context.finalHints context.finalHost).program
      (beforeBoundary context))
  · exact sourceChannels
  · intro interaction used
    rcases closed_program_channels _ _ interaction used with original | check
    · exact List.mem_append_left _ (host_boundary_channels context _ original)
    · rw [check]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The separate verifier retains every original emission and every assertion-check occurrence. -/
private theorem without_verifier_channels_complete (context : Context) :
    ∀ interaction ∈ (withoutCommitments context).verifierOperations.interactions,
      interaction.channel ∈ withoutCommitmentChannels context := by
  apply andThen_channels (baseAssembly context).verifier
    ((FinalMemoryChangeBoundary.closed context.source.sail.memorySnapshot context.target).program (baseAssembly context))
  · intro interaction used
    exact List.mem_append_left _ (base_verifier_channels context interaction used)
  · intro interaction used
    rcases closed_program_channels _ _ interaction used with original | check
    · have same := (change_channels_membership _ _).mp original
      rw [same]
      apply List.mem_append_left
      apply List.mem_append_left
      simp [originalChannels]
    · rw [check]
      exact List.mem_append_right _ List.mem_cons_self

/-- Appending the fixed provider registers no new protocol identity. -/
theorem channels_membership (context : Context) (channel : RawChannel Fp) :
    channel ∈ channels context ↔ channel ∈ (assembly context).channels := by
  have present : CommitmentDeclaration.channel.toRaw ∈ withoutCommitmentChannels context := by
    simp [withoutCommitmentChannels, baseChannels, originalChannels]
  simp only [channels, assembly, CommitmentEnsemble.install, PublicVerifier.install,
    CommitmentEnsemble.withSource, List.mem_append, List.mem_singleton,
    ← without_channels_membership]
  constructor
  · rintro (old | check)
    · exact Or.inl (Or.inl old)
    · exact Or.inr check
  · rintro ((old | declaration) | check)
    · exact Or.inl old
    · exact Or.inl (declaration.symm ▸ present)
    · exact Or.inr check

/-- Both the old verifier and every new statement assertion are in the full registry. -/
theorem verifier_channels_complete (context : Context) :
    ∀ interaction ∈ (assembly context).verifierOperations.interactions,
      interaction.channel ∈ channels context := by
  apply andThen_channels (withoutCommitments context).verifier
    ((CommitmentBoundary.checker context.commitments).program
      (CommitmentEnsemble.withSource context.commitments (withoutCommitments context) (declaration_fresh context)))
  · intro interaction used
    exact List.mem_append_left _ (without_verifier_channels_complete context interaction used)
  · intro interaction used
    have same := checkZeros_channel _ _ interaction used
    rw [same]
    exact List.mem_append_right _ List.mem_cons_self

end SP1CleanTest.Alignment.InstalledAssembly
