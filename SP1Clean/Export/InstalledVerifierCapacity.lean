import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Semantics.Memory.ChangeCapacity

/-! # Verifier costs and thirteen-table mixed-shard capacity

The final memory check has one variable-length stream on its own named channel. All other
verifier traffic is bounded independently of the endpoint contents. This leaves a semantic
preset for the ten preallocated providers and three HINT_READ tables, while other demand
components spend their own measured shared-channel headroom.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Soundness Machine
private def programSize (p : Verifier.Program Fp SP1PublicIO) : Nat := p.circuitOperations.interactions.length

private theorem andThen_size (a b : Verifier.Program Fp SP1PublicIO) : programSize (a.andThen b) = programSize a + programSize b := by
  simp only [programSize, Verifier.Program.andThen, Verifier.Program.circuitOperations, Verifier.Program.operations,
    Verifier.operations_bind, Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append,
    Operations.interactions_append, List.length_append]

private theorem checkZeros_size (name : String) (vs : List (Expression Fp)) :
    (Verifier.checkZeros name vs).circuitOperations.interactions.length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ((Verifier.checkZero name v) >>= fun _ => Verifier.checkZeros name vs).circuitOperations.interactions.length = _
    simp only [VerifierM.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.interactions_append, List.length_append]
    change 2 + (Verifier.checkZeros name vs).circuitOperations.interactions.length = _
    rw [ih, List.length_cons]; omega

private theorem public_size (check : PublicVerifier Fp SP1PublicIO) (ens : Ensemble Fp SP1PublicIO) :
    programSize (check.program ens) = 2 * (check.assertions (varFromOffset SP1PublicIO 0)).length := checkZeros_size _ _

private theorem closed_size (check : ClosedVerifier Fp) (ens : Ensemble Fp SP1PublicIO) :
    programSize (check.program ens) = check.operations.interactions.length + 2 * check.operations.constraints.length := by
  simp only [programSize, ClosedVerifier.program, Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.operations_bind,
    Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append, Operations.interactions_append, List.length_append]
  change check.emit.circuitOperations.interactions.length + (Verifier.checkZeros _ _).circuitOperations.interactions.length = _
  rw [ClosedVerifier.emit_interactions, checkZeros_size]

private theorem emit_size (check : ClosedVerifier Fp) :
    programSize check.interactionProgram = check.operations.interactions.length := congrArg List.length check.emit_interactions

private theorem verifier_length_le (ctx : Context) :
    programSize (assembly ctx).verifier ≤ (ctx.source.sail.memorySnapshot.changes ctx.target.sail.memorySnapshot).length + 1024 := by
  simp only [assembly, base, FixedHintAssembly.assembly, ResourceEnsemble.install, FixedHintAssembly.committedAssembly,
    CommitmentEnsemble.install, CommitmentEnsemble.withSource, FixedHintAssembly.withoutCommitments, Shard.installed,
    HostObserved.ensemble, HostObserved.producers, HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble,
    HostFinalMemory.ensemble, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base, HostHintQueueBoundary.ensemble,
    HaltPadding.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble,
    PublicVerifier.install, ClosedVerifier.install, ClosedVerifier.withInteractions, HostLocalCore.baseEnsemble,
    andThen_size, public_size, closed_size, emit_size, Context.withClock]
  have core : programSize LocalCore.boundaryVerifier ≤ 32 := by exact Nat.le_of_ble_eq_true rfl
  have src : ((LocalSourceBoundary.checker (p := SP1Prime) ctx.image ctx.source).assertions (varFromOffset SP1PublicIO 0)).length ≤ 32 := by exact Nat.le_of_ble_eq_true rfl
  have sail : ((SailBoundary.checker (p := SP1Prime) ctx.source ctx.target).assertions (varFromOffset SP1PublicIO 0)).length = 7 := rfl
  have resource : ((ResourceBoundary.checker (p := SP1Prime) ctx.limits ctx.source ctx.target).assertions (varFromOffset SP1PublicIO 0)).length = 3 := rfl
  have target (head : ℕ) : ((HostHintTarget.checker (p := SP1Prime) ctx.source.host ctx.target.host head).assertions (varFromOffset SP1PublicIO 0)).length = 1 := rfl
  have declaration : ((CommitmentBoundary.checker (p := SP1Prime) ctx.commitments).assertions (varFromOffset SP1PublicIO 0)).length ≤ 128 := by
    simp only [PublicVerifier.assertions, CommitmentBoundary.checker, CommitmentBoundary.circuit, CommitmentBoundary.main, Gadgets.Equality.circuit, Gadgets.Equality.main, circuit_norm]
    change 43 ≤ 128
    decide
  have observation : ((OrdinaryObservation.endpoint (p := SP1Prime) (OrdinaryObservation.startFor ctx.source.sail)
      (OrdinaryObservation.finalFor ctx.source.sail ctx.target.sail)).operations.interactions).length = 2 := rfl
  have hostI (final : HostHintQueue.State Fp) : ((HostHintQueueBoundary.boundary ctx.source final ctx.target.host).operations.interactions).length ≤ 64 := by
    simp only [HostHintQueueBoundary.boundary, ClosedVerifier.operations, HostBoundary.closed, HostBoundary.circuit,
      HostBoundary.main, SP1Clean.HostHintQueueBoundary.circuit, SP1Clean.HostHintQueueBoundary.main,
      HostCommitEndpoint.circuit, HostCommitEndpoint.main, HostCommitBoundary.verifier,
      HostCommitBoundary.verifierMain, HostExitBoundary.circuit, HostExitBoundary.main, GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm]
    change 7 ≤ 64
    decide
  have hostC (final : HostHintQueue.State Fp) : ((HostHintQueueBoundary.boundary ctx.source final ctx.target.host).operations.constraints).length ≤ 32 := by
    simp only [HostHintQueueBoundary.boundary, ClosedVerifier.operations, HostBoundary.closed, HostBoundary.circuit,
      HostBoundary.main, SP1Clean.HostHintQueueBoundary.circuit, SP1Clean.HostHintQueueBoundary.main,
      HostCommitEndpoint.circuit, HostCommitEndpoint.main, HostCommitBoundary.verifier,
      HostCommitBoundary.verifierMain, HostExitBoundary.circuit, HostExitBoundary.main, circuit_norm]
    change 2 ≤ 32
    decide
  have memI : ((FinalMemoryChangeBoundary.closed (p := SP1Prime) ctx.source.sail.memorySnapshot ctx.target.sail.memorySnapshot).operations.interactions).length =
      (ctx.source.sail.memorySnapshot.changes ctx.target.sail.memorySnapshot).length := by
    simp only [ClosedVerifier.operations, FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, FinalMemoryChangeBoundary.raw_interactions, List.length_map]
  have memC : ((FinalMemoryChangeBoundary.closed (p := SP1Prime) ctx.source.sail.memorySnapshot ctx.target.sail.memorySnapshot).operations.constraints).length = 0 := by
    simp only [ClosedVerifier.operations, FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, FinalMemoryChangeBoundary.raw_constraints, List.length_nil]
  rw [sail, resource, target, observation, memI, memC]
  have hostInteractions := hostI (publicCursor ctx)
  have hostConstraints := hostC (publicCursor ctx)
  dsimp only [publicCursor, Context.withClock] at hostInteractions hostConstraints
  omega

private theorem raw_bind (a b : Verifier.Program Fp SP1PublicIO) :
    (a.andThen b).circuitOperations.interactions = a.circuitOperations.interactions ++ b.circuitOperations.interactions := by
  simp only [Verifier.Program.andThen, Verifier.Program.circuitOperations, Verifier.Program.operations,
    Verifier.operations_bind, Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append,
    Operations.interactions_append]

private theorem raw_closed (check : ClosedVerifier Fp) (ens : Ensemble Fp SP1PublicIO) :
    (check.program ens).circuitOperations.interactions = check.operations.interactions ++
    (Verifier.checkZeros (check.channelName ens) check.operations.constraints).circuitOperations.interactions := by
  simp only [ClosedVerifier.program, Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.operations_bind,
    Verifier.Operations.circuitOperations, Verifier.Operations.interactions, List.map_append, Operations.interactions_append]
  change check.emit.circuitOperations.interactions ++ _ = _
  rw [ClosedVerifier.emit_interactions]

private theorem contains_changes (ctx : Context) :
    ((FinalMemoryChangeBoundary.closed (p := SP1Prime) ctx.source.sail.memorySnapshot ctx.target.sail.memorySnapshot).operations.interactions)
      <:+: (assembly ctx).verifierOperations.interactions := by
  unfold Ensemble.verifierOperations
  simp only [assembly, base, FixedHintAssembly.assembly, ResourceEnsemble.install, FixedHintAssembly.committedAssembly,
    CommitmentEnsemble.install, CommitmentEnsemble.withSource, FixedHintAssembly.withoutCommitments, Shard.installed,
    HostObserved.ensemble, HostObserved.producers, HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble,
    HostFinalMemory.ensemble, HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base, HostHintQueueBoundary.ensemble,
    HaltPadding.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble,
    PublicVerifier.install, ClosedVerifier.install, ClosedVerifier.withInteractions, HostLocalCore.baseEnsemble,
    raw_bind, raw_closed, Context.withClock]
  exact (((((List.infix_append_left.trans List.infix_append_right).trans List.infix_append_left).trans
    List.infix_append_left).trans List.infix_append_left).trans List.infix_append_left).trans List.infix_append_left

private def changedKeys (ctx : Context) :=
  ctx.source.sail.memorySnapshot.changes ctx.target.sail.memorySnapshot

private abbrev changeName := (FinalMemoryChange.channel (p := SP1Prime)).name

/-- The actual verifier has bounded constant traffic outside its native changed-location
channel. On that channel it additionally includes one pull for each changed key. -/
theorem verifier_occurrences_le (ctx : Context) (name : String) :
    verifierOccurrences ctx name ≤ 1024 + if name = (FinalMemoryChange.channel (p := SP1Prime)).name then
      (ctx.source.sail.memorySnapshot.changes ctx.target.sail.memorySnapshot).length else 0 := by
  change verifierOccurrences ctx name ≤ 1024 + if name = changeName then (changedKeys ctx).length else 0
  obtain ⟨pre, post, same⟩ := contains_changes ctx
  have size := verifier_length_le ctx
  change (assembly ctx).verifierOperations.interactions.length ≤ (changedKeys ctx).length + 1024 at size
  rw [← same, List.length_append, List.length_append] at size
  rw [verifierOccurrences, ← same, List.countP_append, List.countP_append]
  simp only [ClosedVerifier.operations, FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
    FinalMemoryChangeBoundary.raw_interactions, List.length_map] at size ⊢
  change pre.length + (changedKeys ctx).length + post.length ≤ (changedKeys ctx).length + 1024 at size
  have middle :
      ((List.map (fun key => (FinalMemoryChange.channel.pulled (const key)).toRaw)
        ((changedKeys ctx).map (FinalMemoryChange.encode (p := SP1Prime)))).countP (·.channel.name == name)) =
      (if name = changeName then (changedKeys ctx).length else 0) := by
    rw [List.countP_map, List.countP_map]
    change (changedKeys ctx).countP (fun _ => changeName == name) = _
    by_cases eq : name = changeName
    · simp [eq]
    · simp [Ne.symm eq, eq]
  change pre.countP _ + _ + post.countP _ ≤ _
  simp only [changedKeys] at middle ⊢
  rw [middle, Nat.add_right_comm]
  apply Nat.add_le_add_right
  exact (Nat.add_le_add List.countP_le_length List.countP_le_length).trans (show pre.length + post.length ≤ 1024 by omega)

private theorem change_budget (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (ceiling : ctx.limits.boundaryBytes ≤ 2 ^ 29 + 124) : (changedKeys ctx).length ≤ 2 ^ 30 + 32 := by
  have endpoint (state : ExecutionSnapshot) (fits : state.realize.resources.Fits ctx.limits) :
      (state.sail.memory.supportBelow NativeLayout.sailMemory.upper).card + 125 ≤ ctx.limits.boundaryBytes := by
    rw [state.resources_realize] at fits
    have payload := fits .boundaryBytes
    change state.resources .boundaryBytes ≤ ctx.limits.boundaryBytes at payload
    change (state.sail.memory.supportBelow (2 ^ 48)).card + 125 ≤ ctx.limits.boundaryBytes
    simp only [ExecutionSnapshot.resources, HostState.payloadCost, hintPayloadCost, bytePayloadCost] at payload
    omega
  have source := endpoint ctx.source execution.2.2.2.1
  have target := endpoint ctx.target execution.2.2.2.2.1
  have sparse := MemorySnapshot.changes_length_le_support ctx.source.sail.memorySnapshot ctx.target.sail.memorySnapshot
  change (changedKeys ctx).length ≤ 32 + (ctx.source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card +
    (ctx.target.sail.memory.supportBelow NativeLayout.sailMemory.upper).card at sparse
  omega

private theorem fixed_change (ctx : Context) : additionalOccurrences ctx fixedHeight changeName = 0 := by
  rw [fixed_occurrences]
  simp only [fixedReservations, List.map_cons, List.map_nil, StaticTable.channel, MemorySnapshot.registerTable,
    StaticTable.ofRows, ProgramImage.writePermissionTable, FinalRegisterValue.membership, InitialMemoryLookup.membership]
  rfl

/-- The registered verifier and all fixed providers leave a common reserve. The variable-size
endpoint comparison and the two largest fixed RAM providers charge distinct channels. -/
theorem fixed_verifier_occurrences_le (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (ceiling : ctx.limits.boundaryBytes ≤ 2 ^ 29 + 124) (name : String) :
    verifierOccurrences ctx name + additionalOccurrences ctx fixedHeight name ≤ 2 ^ 30 + 1056 := by
  have verifier := verifier_occurrences_le ctx name
  by_cases same : name = changeName
  · subst name
    rw [fixed_change, Nat.add_zero]
    rw [ite_eq_left rfl] at verifier
    have changed := change_budget ctx execution ceiling
    change (ctx.source.sail.memorySnapshot.changes ctx.target.sail.memorySnapshot).length ≤ 2 ^ 30 + 32 at changed
    omega
  · rw [ite_eq_right same] at verifier
    have fixed := fixed_occurrences_le ctx execution ceiling name
    omega

/-- All ten fixed tables, all three separately padded HINT_READ tables and the complete
verifier jointly fit the preset for arbitrary mixed paths. Every other slot may use the
displayed simultaneous per-channel allowance. -/
theorem fixedProviderPreset_capacity (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (bounded : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤
      SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24) :
    (assembly ctx).interactionsFit .logUp (physicalHeights ctx
      fun t => fixedHeight t + hintReadHeights events t + other t) := by
  have boundary : ctx.limits.boundaryBytes ≤ 2 ^ 29 + 124 := preset.2.2.2.2.2.2.2.2.2.1
  have writes : ctx.limits.writeBytes ≤ 2 ^ 24 := preset.2.2.2.1
  rw [Ensemble.interactionsFit, List.all_eq_true]
  intro ch registered
  simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, total_count, additionalOccurrences_add]
  have fixed := fixed_verifier_occurrences_le ctx execution boundary ch.name
  have hints := (hintRead_occurrences_le ctx execution ch.name).trans (Nat.mul_le_mul_left 14 writes)
  have rest := bounded ch registered
  have enough : (2 ^ 30 + 1056) + 14 * 2 ^ 24 ≤ SP1Prime - 1 := by decide
  omega

/-- The thirteen-table allocation itself fits on every registered channel. -/
theorem fixedProviderPreset_base_fits (ctx : Context) {events : List ExecutionEvent}
    (execution : FormalModel.Shard.AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    (assembly ctx).interactionsFit .logUp (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t) := by
  simpa only [Nat.add_zero] using fixedProviderPreset_capacity ctx execution preset (fun _ => 0)
    (by intro ch registered; simp [additionalOccurrences])

end SP1Clean.Export.InstalledAssembly
