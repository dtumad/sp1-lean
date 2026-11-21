import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.CommitmentEnsemble
import ToClean.Circuit.InteractionRecovery

/-! # The complete-memory assembly only requests commitment declarations

No public-verifier layer of the installed assembly emits on the declaration channel, and its only
physical traffic there consists of the COMMIT/COMMIT_DEFERRED handlers' guarded requests. These
are static facts about the installed circuits, independent of any witness. With the commitment
statement installed above the assembly, they let the verifier-fixed provider authenticate every
request (`CommitmentEnsemble.declared_member`).
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}

/-- The protocols supplied by outer verifier and receipt layers are fresh for the local core. -/
theorem external_not_local {channel : RawChannel (ZMod p)} (outside : channel ∈ externalChannels (p := p)) :
    channel ∉ (LocalCore.baseEnsemble (p := p) image source).channels := by
  intro member
  have used := List.mem_map_of_mem (f := RawChannel.name) member
  simp only [externalChannels, List.mem_cons, List.not_mem_nil, or_false] at outside
  rcases outside with rfl | rfl | rfl <;>
    simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, CommitmentDeclaration.channel,
      InstructionReceipt.channel, OrdinaryObservation.stateChannel, stateChannel, memoryChannel, byteChannel,
      programChannel, exitChannel, syscallChannel, publicValuesChannel, StaticTable.channel,
      InitialMemoryLookup.membership, MemorySnapshot.registerTable, StaticTable.ofRows, Channel.toRaw] at used

private theorem declaration_fresh :
    CommitmentDeclaration.channel.toRaw ∉ (LocalCore.baseEnsemble (p := p) image source).channels :=
  external_not_local (by simp [externalChannels])

omit [Fact (2 ^ 25 < p)] in
/-- A closed boundary that never mentions the declaration channel emits nothing on it. -/
private theorem closed_silent {channel : RawChannel (ZMod p)} (closed : ClosedVerifier (ZMod p))
    (silent : channel ∉ closed.circuit.channels) (env : Environment (ZMod p)) :
    closed.operations.interactionValuesWith channel env = [] := by
  simp only [Operations.interactionValuesWith, ClosedVerifier.operations,
    InteractionRecovery.interactionsWith_main_eq_nil closed.circuit.base _ () 0 silent, List.map_nil]

/-- No underlying verifier emits on the external declarations, receipt, or observation protocol. -/
theorem verifier_external_silent {channel : RawChannel (ZMod p)} (outside : channel ∈ externalChannels (p := p))
    (env : Environment (ZMod p)) :
    (Installed image source target final).verifierOperations.interactionValuesWith
      channel env = [] := by
  let registration := source_registration (p := p) image source target.sail.memorySnapshot
  let original := HostHintReadLocal.ensemble image source HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables target.sail.memorySnapshot)
    (sourceChannels target.sail.memorySnapshot) (source_unique_names image source target.sail.memorySnapshot)
    registration.unique registration.tables
  have declared : channel ∈
      HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: sourceChannels target.sail.memorySnapshot) := by
    have known := external_registered target.sail.memorySnapshot outside
    simp [HostLocalCore.registry, known]
  have originalDeclared : channel ∈ original.channels :=
    List.mem_append_left _ declared
  have boundaryRegistered : (HostHintQueueBoundary.boundary source final target.host).circuit.channels ⊆ original.channels := by
    exact fun _ used => List.mem_append_left _ (registration.boundary
      (HostHintQueueBoundary.boundary_channels_subset source final target.host used))
  let beforeChanges := withReceipts image source target.sail.memorySnapshot final target.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) (sourceChannels target.sail.memorySnapshot)
    (source_unique_names image source target.sail.memorySnapshot) registration
  have changesRegistered : (FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target.sail.memorySnapshot).circuit.channels ⊆ beforeChanges.channels := by
    intro selected used
    apply List.mem_append_left _ (List.mem_append_left _ (registration.targetChannels ?_))
    have equal : selected = FinalMemoryChange.channel.toRaw := by
      simp only [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
        circuit_norm, List.mem_append, List.mem_ofFn, List.mem_singleton] at used
      rcases used with ⟨_, same⟩ | same
      · exact same.symm
      · exact same
    simp [equal, receiptChannels]
  have quiet {other : RawChannel (ZMod p)}
      (absent : other.name ∉ (externalChannels (p := p)).map RawChannel.name) : channel ≠ other :=
    fun eq => absent (eq ▸ List.mem_map_of_mem (f := RawChannel.name) outside)
  change ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target.sail.memorySnapshot).install
    beforeChanges changesRegistered).verifierOperations.interactionValuesWith channel env = []
  rw [ClosedVerifier.install_verifier_interactions_of_mem _ beforeChanges changesRegistered env _
      (List.mem_append_left _ originalDeclared),
    closed_silent _ (by
      intro used
      have same : channel = FinalMemoryChange.channel.toRaw := by
        simp only [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
          circuit_norm, List.mem_append, List.mem_ofFn, List.mem_singleton] at used
        rcases used with ⟨_, same⟩ | same
        · exact same.symm
        · exact same
      exact quiet (of_decide_eq_true rfl) same), List.append_nil]
  change ((HostHintQueueBoundary.boundary source final target.host).install original boundaryRegistered).verifierOperations.interactionValuesWith
    channel env = []
  rw [ClosedVerifier.install_verifier_interactions_of_mem _ original boundaryRegistered env _ originalDeclared,
    closed_silent _ (HostHintQueueBoundary.boundary_silent _
      (quiet (of_decide_eq_true rfl))
      (quiet (of_decide_eq_true rfl))
      (quiet (of_decide_eq_true rfl))
      (quiet (of_decide_eq_true rfl))), List.append_nil]
  change ((LocalSourceBoundary.checker image source).install (HostLocalCore.baseEnsemble image source _ _ _ _ _)).verifierOperations.interactionValuesWith
    channel env = []
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ env _ declared]
  exact LocalCore.boundaryVerifier_silent image source _ (external_not_local outside) env

/-- No underlying verifier emits a commitment declaration. -/
theorem verifier_declarations_silent (env : Environment (ZMod p)) :
    (Installed image source target final).verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = [] :=
  verifier_external_silent (by simp [externalChannels]) env

omit [Fact (2 ^ 25 < p)] in
/-- A component whose channel metadata omits the declaration channel authenticates it vacuously. -/
private theorem authenticates_of_name {property : CommitmentDeclaration.Row (ZMod p) → Prop}
    (component : Component (ZMod p))
    (absent : (component.circuit.channels.map RawChannel.name).contains
      (CommitmentDeclaration.channel (p := p)).toRaw.name = false) :
    component.Authenticates CommitmentDeclaration.channel property := by
  apply Component.Authenticates.of_silent
  intro used
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
  contradiction

/-- A commitment row's only request is a unit pull when active and empty on padding. -/
private theorem commit_authenticates {property : CommitmentDeclaration.Row (ZMod p) → Prop}
    (deferred : Bool) (slot : Fin 8) :
    (HostCallReceivers.commit (p := p) deferred slot).component.Authenticates CommitmentDeclaration.channel
      property := by
  apply Component.Authenticates.of_pulls
  intro env checked interaction member
  have binary := (HostCallReceivers.commit (p := p) deferred slot).activity_of_constraints env checked
  rw [HostCallReceivers.commit_activity] at binary
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((HostCommitChip.circuit deferred slot).main
    (varFromOffset (F := ZMod p) HostCommitChip.RowInput 0)).operations
      (size HostCommitChip.RowInput)).interactionValuesWith CommitmentDeclaration.channel.toRaw env at member
  rw [HostCommitChip.guarded_declaration_values] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.pulledIfValue]
  beta_reduce at binary
  rcases binary with inactive | active
  · exact Or.inl inactive
  · right
    simpa only [Interaction.Pull, true_and] using active

/-- Only the commitment handlers touch the declaration channel, and they only request. -/
theorem declaration_sources (property : CommitmentDeclaration.Row (ZMod p) → Prop)
    (component : Component (ZMod p))
    (member : component ∈ (Installed image source target final).tables) :
    component.Authenticates CommitmentDeclaration.channel property := by
  simp only [Installed, ensemble, ClosedVerifier.install, withReceipts, withRegisters, FinalReceiptEnsemble.install,
    Ensemble.replaceComponent, base, HostHintQueueBoundary.ensemble, HaltPadding.install,
    HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble, PublicVerifier.install,
    HostLocalCore.baseEnsemble] at member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact authenticates_of_name _ rfl
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact authenticates_of_name _ rfl
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact authenticates_of_name _ rfl
  rcases List.mem_append.mp member with core | extra
  · rcases List.mem_or_eq_of_mem_set core with core | rfl
    swap
    · exact authenticates_of_name _ rfl
    rcases List.mem_append.mp core with stores | providers
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      swap
      · exact authenticates_of_name _ rfl
      rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      swap
      · exact authenticates_of_name _ rfl
      rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      swap
      · exact authenticates_of_name _ rfl
      rcases List.mem_or_eq_of_mem_set stores with original | rfl
      swap
      · exact authenticates_of_name _ rfl
      exact Component.Authenticates.of_silent _ _ _ fun used =>
        declaration_fresh (LocalCore.component_channels_subset image source component original used)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at providers
      rcases providers with rfl | rfl
      · apply Component.Authenticates.of_silent
        change CommitmentDeclaration.channel.toRaw ∉
          [image.writePermissionTable.channel.toRaw, WritePermissionProvider.channel.toRaw]
        simp [StaticTable.channel, ProgramImage.writePermissionTable, StaticTable.ofRows,
          WritePermissionProvider.channel, CommitmentDeclaration.channel, Channel.toRaw]
      · apply Component.Authenticates.of_silent
        change CommitmentDeclaration.channel.toRaw ∉ [image.writePermissionTable.channel.toRaw]
        simp [StaticTable.channel, ProgramImage.writePermissionTable, StaticTable.ofRows,
          CommitmentDeclaration.channel, Channel.toRaw]
  · rcases List.mem_append.mp extra with receivers | resources
    · simp only [List.map_cons, List.mem_cons, List.mem_map] at receivers
      rcases receivers with rfl | ⟨view, viewMem, rfl⟩
      · exact authenticates_of_name _ rfl
      · simp only [HostCallReceivers.available, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_ofFn] at viewMem
        rcases viewMem with ((((rfl | rfl) | ⟨slot, rfl⟩) | ⟨slot, rfl⟩) | rfl | rfl)
        · exact authenticates_of_name _ rfl
        · exact authenticates_of_name _ rfl
        · exact commit_authenticates false slot
        · exact commit_authenticates true slot
        · exact authenticates_of_name _ rfl
        · exact authenticates_of_name _ rfl
    · have quiet : (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++
          FinalMemoryChecks.checkTables target.sail.memorySnapshot)).all (fun component : Component (ZMod p) =>
            !(component.circuit.channels.map RawChannel.name).contains
              (CommitmentDeclaration.channel (p := p)).toRaw.name) = true := by
        rfl
      exact authenticates_of_name _ (by simpa using List.all_eq_true.mp quiet component resources)

end SP1Clean.Soundness.HostFinalMemory
