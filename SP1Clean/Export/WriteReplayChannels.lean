import SP1Clean.Export.WriteAllocationSource
import SP1Clean.Export.WriteHintRecordOrigins
import SP1Clean.Export.WriteObservationByte
import SP1Clean.Export.WritePhysicalCuts

/-! # Physical channel evidence for the original CPU and Memory replay -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Channels Semantics Soundness WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

private abbrev registry {e : Ensemble F SP1PublicIO} (_ : EnsembleWitness e) := e.channels

private theorem host_registered (w : EnsembleWitness (base image source target final)) {ch : RawChannel F}
    (reg : ch ∈ registry (hostWitness w)) : ch ∈ registry w := by
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ reg))

private theorem core_registered (w : EnsembleWitness (base image source target final)) {ch : RawChannel F}
    (core : ch ∈ (LocalCore.baseEnsemble image source).channels) : ch ∈ registry w := by
  apply host_registered w
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ core))))

private theorem host_assertion (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (ch : RawChannel F)
    (reg : ch ∈ registry (hostWitness (supervisor (observed w)))) (width : ch.arity = 1) :
    (hostWitness (supervisor (observed w))).BalancedChannel ch := by
  let old := supervisor (observed w)
  let memory := HostObserved.baseWitness old
  let boundary := HostFinalMemory.baseWitness memory
  have ne {other : RawChannel F} (wrong : other.arity ≠ 1) : ch ≠ other := fun same => wrong (same ▸ width)
  have bReg : ch ∈ registry boundary := List.mem_append_left _ reg
  have fmReg : ch ∈ registry memory := List.mem_append_left _ bReg
  have obs := HostObserved.baseWitness_interactions old ch fmReg (ne (by decide)) (ne (by decide))
  have fm := HostFinalMemory.baseWitness_silent_interactions memory ch bReg (ne (by decide)) (ne (by decide)) (ne (by decide))
  have quiet : ch ∉ (HostHintQueueBoundary.boundary source final target.host).circuit.channels := by
    have absent : 1 ∉ (HostHintQueueBoundary.boundaryChannels (p := SP1Prime)).map RawChannel.arity := of_decide_eq_true rfl
    exact fun used => absent (width ▸ List.mem_map_of_mem (f := RawChannel.arity) (HostHintQueueBoundary.boundary_channels_subset source final target.host used))
  have host := HostHintQueueBoundary.projected_silent_interactions boundary ch reg quiet
  have paid := prior_assertion_balance w fit raw ch (host_registered old reg) width
  change BalancedInteractions (old.interactionsWith ch) at paid
  exact Eq.mpr (congrArg BalancedInteractions (host.trans (fm.trans obs))) paid

private theorem old_balance (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (ch : RawChannel F)
    (reg : ch ∈ registry (supervisor (observed w))) (original : ch ≠ WriteProbe.readbackChannel.toRaw)
    (verifier : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name])
    (quiet : ch.name ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    (supervisor (observed w)).BalancedChannel ch := by
  have registered : ch ∈ (preprocessing image source target final).channels := List.mem_append_right _ (List.mem_cons_of_mem _ reg)
  have paid := observed_balance w fit raw ch registered verifier
  change BalancedInteractions ((observed w).interactionsWith ch) at paid
  rwa [unchanged_ledger _ ch original quiet] at paid

private theorem replay_core_balances (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (paid : w.Balanced .logUp) (ch : RawChannel F)
    (member : ch ∈ memoryChannel.toRaw :: programChannel.toRaw :: (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) :
    (supervisor (observed w)).BalancedChannel ch := by
  simp only [SnapshotMemoryEnsemble.membershipChannels,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    apply old_balance w fit paid _ (core_registered _ (by simp [LocalCore.baseEnsemble,sp1Ensemble_channels]))
    all_goals try unfold MemorySnapshot.registerTable
    · exact fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq)
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl

private theorem replay_hint_cursor (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (paid : w.Balanced .logUp) :
    (supervisor (observed w)).BalancedChannel HintReadWordChip.stateChannel.toRaw := by
  have old : HintReadWordChip.stateChannel.toRaw ∈ (base image source target final).channels := by
    apply host_registered (supervisor (observed w))
    apply List.mem_append_left
    simp [HostLocalCore.baseEnsemble,HostLocalCore.registry]
  apply old_balance w fit paid _ old
  · exact fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq)
  · exact of_decide_eq_true rfl
  · exact of_decide_eq_true rfl

/-- The native verifier supplies CPU chronology from the true State and source-check
ledgers and Byte guarantees inherited from the larger verifier and physical inventory. -/
theorem native_cpu_ordering (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness (supervisor (observed w)))) := by
  let old := supervisor (observed w)
  let host := hostWitness old
  have bytes (i : Interaction F) (member : i ∈ host.interactionsWith byteChannel.toRaw) (data : ProverData F) : i.Guarantees data :=
    supervisor_byte_interaction (observed w) ((observed_constraints w).mp ok) (observed_byte_balance w fit raw) i
      ((host_core_ledger old byteChannel.toRaw (by simp [LocalCore.baseEnsemble,sp1Ensemble_channels])) ▸ member) data
  apply HostLocalCore.orderingChannels_of_guarantees host (HostHintReadLocal.auxiliaryInterface (GroundingResources.appendInterface (FinalMemoryChecks.checkTables target.sail.memorySnapshot) (HostHintReadLocal.source_interface source.host.io.hints)))
  · rw [EnsembleWitness.verifierChannelGuarantees_iff_forall]
    exact fun i member => bytes i (EnsembleWitness.mem_interactionsWith.mpr (Or.inl member)) _
  · intro t mt
    rw [t.channelGuarantees_iff_forall]
    exact fun i member => bytes i (EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨t,mt,member⟩)) _
  · exact host_assertion w fit raw _ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
  · have core : stateChannel.toRaw ∈ (LocalCore.baseEnsemble (p := SP1Prime) image source).channels := by simp [LocalCore.baseEnsemble,sp1Ensemble_channels]
    change BalancedInteractions (host.interactionsWith stateChannel.toRaw)
    rw [host_core_ledger old _ core]
    exact old_balance w fit raw _ (core_registered old core) (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "SP1State") eq))
      (of_decide_eq_true rfl) (of_decide_eq_true rfl)

/-- The complete original CPU and HINT read inventories of this physical witness, including
refresh edges at their actual positions in the per-location Memory replay. -/
noncomputable def replayEntries (w : EnsembleWitness (assembly image source target final)) (aligned : List (RowFacts SP1Prime)) :=
  let old := supervisor (observed w)
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness old)
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness old)
  let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness old))
  let additional := ((LocalCore.executionRows core).flatMap (HostHintReadCPU.wordsAt boundary.data words)).map HostHintReadCPU.touch
  MemoryRecordChain.pairs aligned additional (LocalCore.memoryRefreshes core)

/-- All possible observed read-backs use one physical row alignment and one exhaustive,
chronological and source-authenticated Memory chain per location. -/
theorem native_cut_histories (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (paid : w.Balanced .logUp) :
    let old := supervisor (observed w)
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness old)
    let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness old)
    ∃ aligned, List.Forall₂ NativeCore.AlignedFacts aligned ((LocalCore.executionRows core).map (NativeCore.ExecutionRow.facts boundary.data)) ∧
      ∀ loc, CutHistory (MemoryRecordChain.atLocation loc (replayEntries w aligned)) (LocalCore.memoryInitialFrontier core loc)
        (LocalCore.memoryFinalFrontier core loc) (locContent source.sail.realize loc) (QueryAt (WriteSourceRegistry.raw old) loc) := by
  let old := supervisor (observed w)
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness old)
  have checked := (observed_constraints w).mp ok
  have ordering := native_cpu_ordering w ok fit paid
  have valid := (LocalCore.public_contract_of_byte core ordering.sourceChecks ordering.verifierByte).2.1.1.1
  let z := packetSlot image source target final
  exact physical_cut_values valid old (supervisor_constraints _ checked) (z.table (observed w)) (z.table_component _) (z.table_constraints _ checked)
    (native_packet_balance w fit paid) (replay_hint_cursor w fit paid) (assembled_hint_word_data w ok fit paid) (assembled_hint_word_bytes w ok fit paid)
    ordering (replay_core_balances w fit paid _ List.mem_cons_self) (replay_core_balances w fit paid _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun ch member => replay_core_balances w fit paid ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))

end SP1Clean.Export.WriteObservationAssembly
