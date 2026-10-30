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

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

variable {image : ProgramImage} {source : ExecutionSnapshot} {outgoing : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- The declaration channel is fresh for the local core. -/
private theorem declaration_fresh :
    CommitmentDeclaration.channel.toRaw ∉ (LocalCore.baseEnsemble (p := p) image source).channels := by
  intro member
  have used := List.mem_map_of_mem (f := RawChannel.name) member
  simp [LocalCore.baseEnsemble, sp1Ensemble_channels, OrderedBoundary.channel,
    SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, CommitmentDeclaration.channel,
    stateChannel, memoryChannel, byteChannel, programChannel, exitChannel, syscallChannel,
    publicValuesChannel, StaticTable.channel, InitialMemoryLookup.membership, MemorySnapshot.registerTable,
    StaticTable.ofRows, Channel.toRaw] at used

omit [Fact (2 ^ 25 < p)] in
/-- A fresh verifier channel whose stem differs from the declaration name at its fifth character. -/
private theorem fresh_ne_declaration (stem : String) (ens : Ensemble (ZMod p) SP1PublicIO)
    (long : 4 < stem.toList.length) (declaration : stem.toList[4]? ≠ some 'n') :
    VerifierChannel.channel stem ens ≠ CommitmentDeclaration.channel.toRaw := by
  intro same
  have heads := congrArg (fun channel : RawChannel (ZMod p) => channel.name.toList[4]?) same
  dsimp only [VerifierChannel.channel, Verifier.zeroChannel, Channel.toRaw, VerifierChannel.channelName] at heads
  rw [String.toList_append, List.getElem?_append_left long] at heads
  exact declaration (heads.trans (by simp [CommitmentDeclaration.channel]))

omit [Fact (2 ^ 25 < p)] in
/-- A closed boundary that never mentions the declaration channel emits nothing on it. -/
private theorem closed_silent (closed : ClosedVerifier (ZMod p))
    (silent : CommitmentDeclaration.channel.toRaw ∉ closed.circuit.channels) (env : Environment (ZMod p)) :
    closed.operations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = [] := by
  simp only [Operations.interactionValuesWith, ClosedVerifier.operations,
    InteractionRecovery.interactionsWith_main_eq_nil closed.circuit.base _ () 0 silent, List.map_nil]

/-- No public-verifier layer of the installed assembly emits a declaration. -/
theorem verifier_declarations_silent (env : Environment (ZMod p)) :
    (Installed image source outgoing final bankFinal channels).verifierOperations.interactionValuesWith
      CommitmentDeclaration.channel.toRaw env = [] := by
  unfold Installed ensemble
  rw [ClosedVerifier.install_verifier_interactions_of_ne _ _ _ _ (fresh_ne_declaration _ _
      (by rw [show (FinalMemoryChangeBoundary.closed (p := p) source.sail.memorySnapshot outgoing).name =
        "final-memory-change" from rfl]; decide)
      (by rw [show (FinalMemoryChangeBoundary.closed (p := p) source.sail.memorySnapshot outgoing).name =
        "final-memory-change" from rfl]; decide)),
    closed_silent _ (by simp [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
      CommitmentDeclaration.channel, FinalMemoryChange.channel, Channel.toRaw, circuit_norm]), List.append_nil]
  change ((HostHintQueueBoundary.boundary source final bankFinal).install
    (HostHintReadLocal.ensemble image source HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables outgoing)
      channels _)).verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = []
  rw [ClosedVerifier.install_verifier_interactions_of_ne _ _ _ _ (fresh_ne_declaration _ _
      (by rw [show (HostHintQueueBoundary.boundary source final bankFinal).name = "host-boundary" from rfl]; decide)
      (by rw [show (HostHintQueueBoundary.boundary source final bankFinal).name = "host-boundary" from rfl]; decide)),
    closed_silent _ (HostHintQueueBoundary.boundary_silent _
      (by simp [CommitmentDeclaration.channel, HostHintQueue.stateChannel, Channel.toRaw])
      (by simp [CommitmentDeclaration.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [CommitmentDeclaration.channel, HostCommitChip.stateChannel, Channel.toRaw])
      (by simp [CommitmentDeclaration.channel, HostExitBoundary.channel, Channel.toRaw])), List.append_nil]
  change ((LocalSourceBoundary.checker image source).install (HostLocalCore.baseEnsemble image source _ _ _)).verifierOperations.interactionValuesWith
    CommitmentDeclaration.channel.toRaw env = []
  rw [PublicVerifier.install_verifier_interactions _ _ _ _ (fresh_ne_declaration _ _
    (by rw [show (LocalSourceBoundary.checker (p := p) image source).name = "sp1.local.source" from rfl]; decide)
    (by rw [show (LocalSourceBoundary.checker (p := p) image source).name = "sp1.local.source" from rfl]; decide))]
  exact LocalCore.boundaryVerifier_silent image source _ declaration_fresh env

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
  · exact Or.inl (by rw [inactive, neg_zero])
  · exact Or.inr (congrArg Neg.neg active)

/-- Only the commitment handlers touch the declaration channel, and they only request. -/
theorem declaration_sources (property : CommitmentDeclaration.Row (ZMod p) → Prop)
    (component : Component (ZMod p))
    (member : component ∈ (Installed image source outgoing final bankFinal channels).tables) :
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
          FinalMemoryChecks.checkTables outgoing)).all (fun component : Component (ZMod p) =>
            !(component.circuit.channels.map RawChannel.name).contains
              (CommitmentDeclaration.channel (p := p)).toRaw.name) = true := by
        rfl
      exact authenticates_of_name _ (by simpa using List.all_eq_true.mp quiet component resources)

end SP1Clean.Soundness.HostFinalMemory
