import SP1Clean.Soundness.HostHintReadLocalRecords
import SP1Clean.Soundness.FinalMemoryChecks
import SP1Clean.Native.Operations.InstructionReceipt
import SP1Clean.FormalModel.Contracts.OrdinaryObservation

/-! # Static registry of the complete-memory host inventory

The installed host registry and both target validators keep distinct canonical names, and the
validators have a proved static host-resource interface. The source-backed host proofs are stated
over this one inventory, so these facts sit below them.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalNamesLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The complete physical host inventory has distinct canonical names before receipt wrapping. -/
abbrev UniqueNames (image : ProgramImage) (source : ExecutionSnapshot) (extra : List (Component (ZMod p)))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) : Prop :=
  ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ (resources ++ extra)))).map
      (·.circuit.name)).Nodup

/-- Static channel coverage and unique protocol names for the complete host inventory. -/
class Registration (image : ProgramImage) (source : ExecutionSnapshot) (extra : List (Component (ZMod p)))
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Prop where
  unique : ((HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels)).map (·.name)).Nodup
  tables : ∀ component ∈ (HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ (resources ++ extra)),
    component.circuit.channels ⊆ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels)
  boundary : [HostHintQueue.stateChannel.toRaw, (HostCommitChip.stateChannel false).toRaw,
      (HostCommitChip.stateChannel true).toRaw, HostExitBoundary.channel.toRaw] ⊆
    HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels)

/-- Finalizers hand these three protocols to the outgoing memory checks. -/
def receiptChannels : List (RawChannel (ZMod p)) :=
  [(FinalMemoryValue.channel false).toRaw, (FinalMemoryValue.channel true).toRaw, FinalMemoryChange.channel.toRaw]

/-- Channels supplied above the complete-memory host proof view. -/
def externalChannels : List (RawChannel (ZMod p)) :=
  [CommitmentDeclaration.channel.toRaw, InstructionReceipt.channel.toRaw, OrdinaryObservation.stateChannel.toRaw]

/-- Target consumers register both receipt protocols and the change protocol. -/
theorem Registration.targetChannels {image : ProgramImage} {source : ExecutionSnapshot}
    {target : MemorySnapshot} {others : List (HostLocalHandoff.Receiver (p := p))}
    {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (registered : Registration image source (FinalMemoryChecks.checkTables target) others resources channels) :
    receiptChannels ⊆ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: channels) := by
  intro channel member
  simp only [receiptChannels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · apply registered.tables ((FinalMemoryChecks.checkTables target)[0]'(by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega))
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.getElem_mem (by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega)))))
    change _ ∈ [_, (FinalMemoryValue.channel false).toRaw] ++ [_ , _]
    simp
  · apply registered.tables ((FinalMemoryChecks.checkTables target)[1]'(by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega))
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.getElem_mem (by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega)))))
    simp only [FinalMemoryChecks.checkTables, List.getElem_cons_succ, List.getElem_cons_zero]
    apply List.mem_append_right
    exact List.mem_cons_self ..
  · apply registered.tables ((FinalMemoryChecks.checkTables target)[0]'(by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega))
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.getElem_mem (by simp only [FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]; omega)))))
    change _ ∈ [_, _] ++ [_, FinalMemoryChange.channel.toRaw]
    simp

/-- Each host protocol is registered once; shared core channels are inherited from the core.
The ordinary receipt and observation protocols are registered here with their future consumer;
their producers are installed above this inventory. -/
def sourceChannels (target : MemorySnapshot) : List (RawChannel (ZMod p)) :=
  [HostHintQueue.wordChannel.toRaw, HostHintQueue.nodeChannel.toRaw, HostHintQueue.stateChannel.toRaw,
    HostExitBoundary.channel.toRaw, (HostCommitChip.stateChannel false).toRaw,
    (HostCommitChip.stateChannel true).toRaw, HostRamAccessChip.channel.toRaw] ++ receiptChannels ++
    [(FinalRegisterValue.membership target).channel.toRaw,
      (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw] ++ externalChannels

omit [Fact (2 ^ 25 < p)] in
/-- The registry includes every protocol supplied by the outer assembly. -/
theorem external_registered (target : MemorySnapshot) : externalChannels ⊆ sourceChannels (p := p) target :=
  fun _ => List.mem_append_right _

/-- Indices of the complete raw channel declarations for the physical host suffix.
Repeated declarations remain here; the registry they index contains each protocol once. -/
private def sourceChannelIndices : List (List (Fin 30)) :=
  [[8, 8, 15, 8, 8, 16, 0, 17, 14, 16, 15, 0, 17, 14], [8, 0, 0, 18], [0, 0], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 19, 27, 0, 19, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [8, 8, 27, 0, 20, 27, 0, 20, 13], [16, 0, 17, 0, 17, 16], [0, 17, 0, 17], [8, 10, 15, 8, 8, 21, 1, 1, 1, 1, 1, 1, 1, 1, 14, 10, 21, 15, 1, 14], [8, 10, 15, 8, 8, 21, 1, 1, 1, 1, 1, 1, 1, 1, 14, 10, 21, 15, 1, 14], [16], [15], [19, 19], [20, 20], [8, 8, 8, 8, 28, 29, 28, 29], [29, 29], [29, 29], [29, 29], [25, 22, 22, 24], [26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 8, 8, 8, 8, 26, 8, 23, 23, 24], [25], [26]]

private theorem source_channel_declarations (image : ProgramImage) (source : ExecutionSnapshot)
    (target : MemorySnapshot) (includeVerify : Bool := true) :
    (((HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.availableFor includeVerify).map (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
      (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++
        FinalMemoryChecks.checkTables target))).map (fun component : Component (ZMod p) => component.circuit.channels)) =
      sourceChannelIndices.map (fun indices => indices.map (fun index =>
        (HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: sourceChannels target))[index.val]'(by
          change index.val < 30
          exact index.isLt))) := by
  cases includeVerify <;> repeat' first
    | apply congrArg₂ List.cons
    | rfl

/-- The standard source-backed host assembly has complete, unique channel registration. -/
theorem source_registration (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot) (includeVerify : Bool := true) :
    Registration (p := p) image source (FinalMemoryChecks.checkTables target) (HostCallReceivers.availableFor includeVerify)
      (HostHintReadLocal.sourceResources source.host.io.hints) (sourceChannels target) := by
  constructor
  · simp only [HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels,
      sourceChannels, receiptChannels, externalChannels, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, StaticTable.channel, StaticTable.ofRows, MemorySnapshot.registerTable,
      ProgramImage.writePermissionTable, InitialMemoryLookup.membership, FinalRegisterValue.membership,
      Channel.toRaw_name]
    dsimp only [HostCallChip.channel, WritePermissionProvider.channel, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      stateChannel, byteChannel, programChannel, memoryChannel, exitChannel, syscallChannel, publicValuesChannel,
      HintReadWordChip.stateChannel, HostHintQueue.wordChannel, HostHintQueue.nodeChannel, HostHintQueue.stateChannel,
      HostExitBoundary.channel, HostCommitChip.stateChannel, HostRamAccessChip.channel, FinalMemoryValue.channel,
      FinalMemoryChange.channel, CommitmentDeclaration.channel, InstructionReceipt.channel, OrdinaryObservation.stateChannel]
    decide
  · intro component member channel used
    have declared := List.mem_map_of_mem
      (f := fun component : Component (ZMod p) => component.circuit.channels) member
    rw [source_channel_declarations image source target includeVerify] at declared
    obtain ⟨indices, _, equal⟩ := List.mem_map.mp declared
    rw [← equal] at used
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp used
    exact List.getElem_mem _
  · simp [HostLocalCore.registry, sourceChannels]

attribute [instance] source_registration

/-- The concrete host registry and both target validators have distinct canonical names. -/
theorem source_unique_names (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot) (includeVerify : Bool := true) :
    UniqueNames (p := p) image source (FinalMemoryChecks.checkTables target) (HostCallReceivers.availableFor includeVerify)
      (HostHintReadLocal.sourceResources source.host.io.hints) := by
  let original := HostLocalCore.tables (p := p) image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.availableFor includeVerify).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources source.host.io.hints))
  have split : ((HostLocalCore.tables (p := p) image source
      ((HostHintReadHandoff.receiver :: HostCallReceivers.availableFor includeVerify).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++
          FinalMemoryChecks.checkTables target)))).map (·.circuit.name)) =
      original.map (·.circuit.name) ++ (FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name) := by
    simp only [original, HostLocalCore.tables_names, List.map_append, List.append_assoc]
  rw [UniqueNames, split, List.nodup_append]
  refine ⟨HostHintReadLocal.source_unique_names image source source.host.io.hints includeVerify,
    ?_, ?_⟩
  · simp only [FinalMemoryChecks.checkTables, List.map_cons, List.map_nil,
      StaticTable.component, StaticTable.provider, FinalRegisterValue.membership]
    exact of_decide_eq_true rfl
  · have fresh : (original.map (·.circuit.name)).all
        (fun name => !((FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name)).contains name) = true := by
      simp only [original, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
        LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
        SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
        MemorySnapshot.registerTable, StaticTable.ofRows,
        FinalMemoryChecks.checkTables, FinalRegisterValue.membership]
      cases includeVerify <;> rfl
    intro a old b added same
    have absent := List.all_eq_true.mp fresh a old
    rw [List.contains_iff_mem.mpr (same.symm ▸ added)] at absent
    exact Bool.noConfusion absent

omit [Fact (2 ^ 25 < p)] in
/-- A component without a Byte requirement discharges its Byte requirement vacuously. -/
theorem not_required (component : Component (ZMod p))
    (quiet : (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = false)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _ (component.inChannelsOrRequirements_of_constraints env checked)
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = true at present
  rw [quiet] at present
  contradiction

end SP1Clean.Soundness.HostFinalMemory
