import SP1Clean.Soundness.NativeCoreEnsemble
import SP1Clean.Soundness.SnapshotMemoryEnsemble
import SP1Clean.FormalModel.Contracts.LocalCoreBoundary

/-! # Native local-shard assembly with a checked complete source

This assembly installs source register/RAM tables alongside the existing finalizers, fixed ROM,
instructions, and providers. The verifier checks the finite program, supported decoding, complete
Sail platform configuration and register initialization, source ROM, and 48-bit source PC/clock.
It binds the public incoming State token to that actual PC and clock; outgoing fields are range
checked. A stopped source must retain the same clock at the public end, excluding active events
through strict State ordering while admitting identity segments. ROM is checked even at bytes
absent from the touched inventory.

Byte and Program closure follow from this assembly's own raw ledger. Source State truth and the
initial memory invariant are derived in `LocalCoreSourceGrounding`. The mixed host walk, complete
outgoing state, and witness composition remain open; this assembly is not yet an execution theorem.
Host state and Sail bookkeeping are retained source data, without a reset at a shard cut.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

def verifierMain (image : ProgramImage) (source : ExecutionSnapshot)
    (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← sp1StateVerifier input
  assertZero (.const (if checkExecutionSource image source then 0 else 1))
  assertZero (input.init_clk_high - .const (source.clock / 2 ^ 24 : ℕ))
  assertZero (input.init_clk_low - .const (source.clock % 2 ^ 24 : ℕ))
  assertZero (input.init_pc0 - .const (Target.bitVecToWord source.pc)[0])
  assertZero (input.init_pc1 - .const (Target.bitVecToWord source.pc)[1])
  assertZero (input.init_pc2 - .const (Target.bitVecToWord source.pc)[2])
  let stopped : Expression (ZMod p) := .const (if source.host.exitCode = none then 0 else 1)
  assertZero (stopped * (input.final_clk_high - input.init_clk_high))
  assertZero (stopped * (input.final_clk_low - input.init_clk_low))
  let _ ← OrderedBoundaryVerifier.circuit SnapshotMemoryEnsemble.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()
  let _ ← OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()

def verifier (image : ProgramImage) (source : ExecutionSnapshot) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := verifierMain image source
  Spec input _ _ := input.LimbBounds ∧ ExecutionSourceValid image source ∧
    input.SourceFor source ∧ input.PreservesStoppedClock source
  ProverAssumptions input data hint :=
    sp1StateVerifier.ProverAssumptions input data hint ∧ ExecutionSourceValid image source ∧
      input.SourceFor source ∧ input.PreservesStoppedClock source
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, OrderedBoundaryVerifier.circuit,
      SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock]
    obtain ⟨bounds, checked, hi, lo, pc0, pc1, pc2, stoppedHi, stoppedLo⟩ := h_holds
    have valid : ExecutionSourceValid image source := by
      by_cases valid : checkExecutionSource image source = true
      · exact (checkExecutionSource_iff image source).mp valid
      · simp [valid] at checked
    refine ⟨bounds, valid, ?_, ?_⟩
    · exact ⟨sub_eq_zero.mp hi, sub_eq_zero.mp lo, sub_eq_zero.mp pc0,
        sub_eq_zero.mp pc1, sub_eq_zero.mp pc2⟩
    · intro stopped
      simpa [stopped, sub_eq_zero] using And.intro stoppedHi stoppedLo
  completeness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, OrderedBoundaryVerifier.circuit,
      SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock]
    obtain ⟨ordinary, valid, binding, stopped⟩ := h_assumptions
    have fields := binding
    refine ⟨ordinary, by simp [(checkExecutionSource_iff image source).mpr valid],
      sub_eq_zero.mpr fields.1, sub_eq_zero.mpr fields.2.1,
      sub_eq_zero.mpr fields.2.2.1, sub_eq_zero.mpr fields.2.2.2.1,
      sub_eq_zero.mpr fields.2.2.2.2, ?_, ?_⟩
    · by_cases running : source.host.exitCode = none
      · simp [running]
      · simp [running, (stopped running).1]
    · by_cases running : source.host.exitCode = none
      · simp [running]
      · simp [running, (stopped running).2]

def tables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component) ++ NativeCore.afterInitialTables image

def ensemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source
  channels := (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: sp1Ensemble.channels
  verifier := verifier image source
  verifier_length_zero := by intros; rfl

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).length = 59 := by
  simp [tables, SnapshotMemoryEnsemble.inventory, NativeCore.afterInitialTables,
    OrderedMemoryEnsemble.Inventory.views, FinalMemoryEnsemble.inventory,
    sp1Tables_length, sp1ProviderTables_length]

private theorem source_requirements (source : ExecutionSnapshot) (component : Component (ZMod p))
    (member : component ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw] := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [SnapshotMemoryEnsemble.registerView, SnapshotMemoryEnsemble.ramView,
      SnapshotMemoryEnsemble.terminalView, OrderedMemoryEnsemble.providerView,
      OrderedMemoryEnsemble.terminalView, OrderedMemoryProvider.circuit,
      OrderedBoundaryEnd.circuit, SnapshotRegisterProvider.circuit, SnapshotRamProvider.circuit]

private theorem component_finished_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).allTables)
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
      have used := source_requirements source component member required
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
      tauto))
  · exact NativeCore.afterInitialTables_finished_requirements image component member channel outside env constraints

/-- The local assembly supplies its own Byte and Program guarantees, including for both
source providers. No provider validity or memory-content premise is accepted here. -/
theorem finishedChannel_guarantees (image : ProgramImage) (source : ExecutionSnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables,
      table.ChannelGuarantees byteChannel.toRaw ∧ table.ChannelGuarantees programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (ensemble (p := p) image source).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
        (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]) :=
    witness.channelGuarantees_of_component_requirements channel constraints (balanced channel member)
      (fun component mem env holds => component_finished_requirements image source component mem channel outside env holds)
  have byte := closed byteChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, byteChannel])
  have program := closed programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
      OrderedFinalProvider.channelName, programChannel])
  exact fun table member => ⟨byte table member, program table member⟩

/-- Program guarantees use only this channel's balance, so host extensions can retain their
complete Memory ledger while reusing the fixed program provider. -/
theorem program_guarantees_of_balance (image : ProgramImage) (source : ExecutionSnapshot)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees programChannel.toRaw :=
  witness.channelGuarantees_of_component_requirements programChannel.toRaw constraints balanced
    (fun component mem env holds => component_finished_requirements image source component mem
      programChannel.toRaw (by simp [circuit_norm, OrderedBoundary.channel,
        SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, programChannel]) env holds)

/-- Exactly the channel facts used by chronology. Byte guarantees may be transported from a
larger ensemble without projecting its Byte multiplicities or its Memory effects. -/
structure OrderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : Prop where
  byte : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw
  state : witness.BalancedChannel stateChannel.toRaw

/-- A static local-component interface for deriving Byte guarantees in a larger assembly. -/
theorem component_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).allTables)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  apply component_finished_requirements image source component member byteChannel.toRaw ?_ env constraints
  simp [circuit_norm, OrderedBoundary.channel, SnapshotMemoryEnsemble.channelName,
    OrderedFinalProvider.channelName, byteChannel]

/-- The local assembly derives the ordering interface from its Byte and State ledgers alone. -/
theorem orderingChannels_of_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) (constraints : witness.Constraints)
    (byte : witness.BalancedChannel byteChannel.toRaw) (state : witness.BalancedChannel stateChannel.toRaw) :
    OrderingChannels witness := by
  refine ⟨?_, state⟩
  apply witness.channelGuarantees_of_component_requirements byteChannel.toRaw constraints byte
  intro component member env checked
  exact component_byte_requirements image source component member env checked

/-- Existing complete witnesses supply the smaller chronology interface. -/
theorem orderingChannels_of_balanced {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) : OrderingChannels witness :=
  orderingChannels_of_constraints witness constraints
    (balanced _ (by simp [ensemble, sp1Ensemble_channels]))
    (balanced _ (by simp [ensemble, sp1Ensemble_channels]))

end SP1Clean.Soundness.LocalCore
