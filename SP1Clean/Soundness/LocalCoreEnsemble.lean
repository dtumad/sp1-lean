import SP1Clean.Soundness.NativeCoreEnsemble
import SP1Clean.Soundness.SnapshotMemoryEnsemble
import SP1Clean.Model.Core.SourceSnapshot

/-! # Native local-shard assembly with an authenticated source snapshot

This assembly installs the actual snapshot register/RAM tables alongside the existing finalizers,
fixed ROM, instructions, and providers. Its public PC/clock endpoints are range checked rather
than fixed to boot. The verifier checks the finite program, supported decoding, source x0, and
every ROM byte in source memory, including bytes absent from the touched inventory.

Byte and Program closure are proved from this assembly's own raw ledger. This is not yet an
execution theorem: complete Sail/host endpoint binding, final-state agreement, source-time
admissibility, and the mixed host walk remain to be connected. The boot assembly remains a proved
specialized client of the same instruction/provider suffix during that transport.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

def verifierMain (image : ProgramImage) (snapshot : MemorySnapshot)
    (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← sp1StateVerifier input
  assertZero (.const (if checkSource image snapshot then 0 else 1))
  let _ ← OrderedBoundaryVerifier.circuit SnapshotMemoryEnsemble.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()
  let _ ← OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()

def verifier (image : ProgramImage) (snapshot : MemorySnapshot) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := verifierMain image snapshot
  Spec input _ _ := input.LimbBounds ∧ SourceValid image snapshot
  ProverAssumptions input data hint :=
    sp1StateVerifier.ProverAssumptions input data hint ∧ SourceValid image snapshot
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, OrderedBoundaryVerifier.circuit]
    by_cases valid : checkSource image snapshot = true
    · exact ⟨h_holds.1, (checkSource_iff image snapshot).mp valid⟩
    · simp [valid] at h_holds
  completeness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, OrderedBoundaryVerifier.circuit]
    exact ⟨h_assumptions.1, by simp [(checkSource_iff image snapshot).mpr h_assumptions.2]⟩

def tables (image : ProgramImage) (snapshot : MemorySnapshot) : List (Component (ZMod p)) :=
  (SnapshotMemoryEnsemble.inventory snapshot).views.map (·.component) ++ NativeCore.afterInitialTables image

def ensemble (image : ProgramImage) (snapshot : MemorySnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image snapshot
  channels := (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: sp1Ensemble.channels
  verifier := verifier image snapshot
  verifier_length_zero := by intros; rfl

theorem tables_length (image : ProgramImage) (snapshot : MemorySnapshot) :
    (tables (p := p) image snapshot).length = 59 := by
  simp [tables, SnapshotMemoryEnsemble.inventory, NativeCore.afterInitialTables,
    OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
    sp1Tables_length, sp1ProviderTables_length]

private theorem source_requirements (snapshot : MemorySnapshot) (component : Component (ZMod p))
    (member : component ∈ (SnapshotMemoryEnsemble.inventory snapshot).views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw] := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [SnapshotMemoryEnsemble.registerView, SnapshotMemoryEnsemble.ramView,
      SnapshotMemoryEnsemble.terminalView, OrderedMemoryEnsemble.providerView,
      OrderedMemoryEnsemble.terminalView, OrderedMemoryProvider.circuit,
      OrderedBoundaryEnd.circuit, SnapshotRegisterProvider.circuit, SnapshotRamProvider.circuit]

private theorem component_finished_requirements (image : ProgramImage) (snapshot : MemorySnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image snapshot).allTables)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  simp only [Ensemble.allTables, ensemble, tables, List.mem_cons, List.mem_append] at member
  rcases member with rfl | member | member
  · exact absent (by simp [Ensemble.verifierTable, verifier])
  · exact absent (fun required => outside (by
      have used := source_requirements snapshot component member required
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
      tauto))
  · exact NativeCore.afterInitialTables_finished_requirements image component member channel outside env constraints

/-- The local assembly supplies its own Byte and Program guarantees, including for both
snapshot providers. No provider validity or memory-content premise is accepted here. -/
theorem finishedChannel_guarantees (image : ProgramImage) (snapshot : MemorySnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image snapshot))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables,
      table.ChannelGuarantees byteChannel.toRaw ∧ table.ChannelGuarantees programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (ensemble (p := p) image snapshot).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
        (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]) :=
    witness.channelGuarantees_of_component_requirements channel constraints (balanced channel member)
      (fun component mem env holds => component_finished_requirements image snapshot component mem channel outside env holds)
  have byte := closed byteChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, byteChannel])
  have program := closed programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, programChannel])
  exact fun table member => ⟨byte table member, program table member⟩

end SP1Clean.Soundness.LocalCore
