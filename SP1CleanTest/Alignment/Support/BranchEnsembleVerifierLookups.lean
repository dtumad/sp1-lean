import SP1CleanTest.Alignment.Support.BranchEnsembleFixture

/-! # Lookup-free public verifier of the complete branch assembly

The target-dependent change inventory emits interactions only. The proof retains its arbitrary
finite key list and the original core/host verifier composition.
-/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness

private theorem change_lookups (keys : List (FinalMemoryChange.Key Fp)) (offset : ℕ) :
    ((FinalMemoryChangeBoundary.main keys ()).operations offset).lookups = [] := by
  rw [FinalMemoryChangeBoundary.operations]
  induction keys with
  | nil => rfl
  | cons key rest ih => simpa only [List.map_cons, circuit_norm] using ih

/-- The actual closed verifier contains no lookup, for every complete target snapshot. -/
theorem verifier_lookups (target : MemorySnapshot) :
    (assembly target).verifierTable.rowOperations.lookups = [] := by
  simp only [assembly, HostFinalMemory.ensemble, ClosedVerifier.install,
    Ensemble.verifierTable, Component.rowOperations, ClosedVerifier.verifier,
    ClosedVerifier.verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_lookups,
    FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, change_lookups]
  simp only [HostFinalMemory.withReceipts, HostFinalMemory.withRegisters,
    FinalReceiptEnsemble.install, HostFinalMemory.base, HostHintQueueBoundary.ensemble,
    HaltPadding.install, ClosedVerifier.install, HostHintReadLocal.ensemble,
    HostLocalHandoff.ensemble, HostLocalCore.ensemble, ClosedVerifier.verifier,
    ClosedVerifier.verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_lookups]
  simp only [LocalCore.verifier, LocalCore.verifierMain, sp1StateVerifier,
    OrderedBoundaryVerifier.circuit, OrderedBoundaryVerifier.main, HostBoundary.main,
    HostHintQueueBoundary.circuit, HostHintQueueBoundary.main, HostCommitEndpoint.circuit,
    HostCommitEndpoint.main, HostCommitBoundary.verifier, HostCommitBoundary.verifierMain,
    HostExitBoundary.circuit, HostExitBoundary.main, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_lookups]

end SP1Clean.Audit.BranchEnsemble
