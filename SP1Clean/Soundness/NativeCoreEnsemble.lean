import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.InitialMemoryEnsemble
import SP1Clean.Soundness.FinalMemoryEnsemble
import SP1Clean.Proofs.Chips.DecodedProgramProvider.Bridge
import SP1Clean.FormalModel.Contracts.NativeCoreBoundary

/-! # Image-authenticated native core assembly

This assembly replaces the legacy Program and memory-boundary providers with the fixed decoded
ROM and the ordered register/RAM inventories. The verifier fixes boot PC/time and both private
ordering boundaries. Byte/Program closure uses the actual combined ledger. Connecting this
assembly to mixed-row timed grounding and the complete host environment remains separate work;
this module does not claim an execution theorem for the assembly.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

def verifierMain (image : ProgramImage) (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← sp1StateVerifier input
  assertZero input.init_clk_high
  assertZero (input.init_clk_low - 1)
  assertZero (input.init_pc0 - .const (bitVecToWord image.entry)[0])
  assertZero (input.init_pc1 - .const (bitVecToWord image.entry)[1])
  assertZero (input.init_pc2 - .const (bitVecToWord image.entry)[2])
  let _ ← OrderedBoundaryVerifier.circuit OrderedInitialProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()
  let _ ← OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()

def verifier (image : ProgramImage) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := verifierMain image
  Spec input _ _ := input.LimbBounds ∧ input.BootFor image
  ProverAssumptions input data hint :=
    sp1StateVerifier.ProverAssumptions input data hint ∧ input.BootFor image
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, SP1PublicIO.BootFor,
      OrderedBoundaryVerifier.circuit]
    simpa only [sub_eq_zero] using h_holds
  completeness := by
    circuit_proof_start [verifierMain, sp1StateVerifier, SP1PublicIO.BootFor,
      OrderedBoundaryVerifier.circuit]
    simpa only [sub_eq_zero] using h_assumptions

/-- The remaining core components, after the initialization inventory. -/
def afterInitialTables (image : ProgramImage) : List (Component (ZMod p)) :=
  FinalMemoryEnsemble.inventory.views.map (·.component) ++
    [⟨DecodedProgramProvider.circuit image⟩] ++ sp1Tables ++
    (sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26)

/-- Both memory inventories precede ordinary instructions; the order is an assembly detail.
The legacy unauthenticated Program/init/final providers are absent. -/
def tables (image : ProgramImage) : List (Component (ZMod p)) :=
  (InitialMemoryEnsemble.views image).map (·.component) ++ afterInitialTables image

def ensemble (image : ProgramImage) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image
  channels := (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ::
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: sp1Ensemble.channels
  verifier := verifier image
  verifier_length_zero := by intros; rfl

theorem tables_length (image : ProgramImage) : (tables (p := p) image).length = 59 := by
  simp [tables, afterInitialTables, InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, sp1Tables_length, sp1ProviderTables_length]

private theorem boundary_requirements (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (InitialMemoryEnsemble.views image).map (·.component) ++
      FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.circuit.channelsWithRequirements ⊆
      [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw] := by
  simp only [InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    simp [InitialMemoryEnsemble.registerView, InitialMemoryEnsemble.ramView,
      InitialMemoryEnsemble.providerView, InitialMemoryEnsemble.terminalView,
      FinalMemoryEnsemble.viewFor, FinalMemoryEnsemble.registerView, FinalMemoryEnsemble.ramView,
      OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
      OrderedMemoryProvider.circuit, OrderedBoundaryEnd.circuit,
      InitialRegisterProvider.circuit, InitialRamProvider.circuit,
      FinalRegisterProvider.circuit, FinalRamProvider.circuit]

/-- The shared instruction/finalizer/provider suffix closes Byte and Program requirements.
This proof is independent of the choice of source inventory and boot/local verifier. -/
theorem afterInitialTables_finished_requirements (image : ProgramImage)
    (component : Component (ZMod p)) (member : component ∈ afterInitialTables (p := p) image)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw])
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements channel env := by
  have absent (notRequired : channel ∉ component.circuit.channelsWithRequirements) :
      component.operations.ChannelRequirements channel env :=
    Operations.requirements_of_not_mem _ _ _
      (component.inChannelsOrRequirements_of_constraints env constraints) channel notRequired
  have old (member : component ∈ (sp1Ensemble (p := p)).allTables) :=
    sp1_component_finished_requirements component member channel
      (fun mem => outside (by simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢; tauto))
      env constraints
  simp only [afterInitialTables, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at member
  rcases member with ((member | rfl) | member) | member
  · exact absent (fun required => outside (List.mem_cons_of_mem _
      (boundary_requirements image component (List.mem_append_right _ member) required)))
  · have required := (Component.weakSoundness_of_no_guarantees
      (⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)) rfl (by trivial) constraints).2
    exact fun interaction emitted _ => required interaction emitted
  · exact old (Ensemble.mem_allTables_of_mem_tables (by
      rw [sp1Ensemble_tables]; exact List.mem_append_left _ member))
  · have providerMem : component ∈ sp1ProviderTables (p := p) := by
      rcases member with member | member
      · exact List.mem_of_mem_take member
      · exact List.mem_of_mem_drop member
    exact old (Ensemble.mem_allTables_of_mem_tables (by
      rw [sp1Ensemble_tables]; exact List.mem_append_right _ providerMem))

/-- New boundary tables preserve closure of Byte/Program: their only outgoing nontrivial
requirements are Memory. The fixed Program provider proves its own requirements. -/
private theorem component_finished_requirements (image : ProgramImage)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image).allTables)
    (channel : RawChannel (ZMod p))
    (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
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
  · exact absent (fun required => outside (List.mem_cons_of_mem _
      (boundary_requirements image component (List.mem_append_left _ member) required)))
  · exact afterInitialTables_finished_requirements image component member channel outside env constraints

/-- Every table in the combined assembly receives proved Byte and Program guarantees from
raw constraints and actual channel balance. This includes the new memory boundary circuits. -/
theorem finishedChannel_guarantees (image : ProgramImage)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables,
      table.ChannelGuarantees byteChannel.toRaw ∧ table.ChannelGuarantees programChannel.toRaw := by
  have closed (channel : RawChannel (ZMod p)) [channel.Consistent]
      (member : channel ∈ (ensemble (p := p) image).channels)
      (outside : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]) :=
    witness.channelGuarantees_of_component_requirements channel constraints (balanced channel member)
      (fun component mem env holds => component_finished_requirements image component mem channel outside env holds)
  have byte := closed byteChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, OrderedInitialProvider.channelName,
      OrderedFinalProvider.channelName, byteChannel])
  have program := closed programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels]) (by
    simp [circuit_norm, OrderedBoundary.channel, OrderedInitialProvider.channelName,
      OrderedFinalProvider.channelName, programChannel])
  exact fun table member => ⟨byte table member, program table member⟩

end SP1Clean.Soundness.NativeCore
