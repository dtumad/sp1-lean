import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.HostCallProjection
import SP1Clean.Soundness.HostCallOrder

/-! # Local AIR with the instruction-to-host wrapper installed

The protected local assembly retains its verifier, source/final inventories, ordinary chips,
and permission provider. Its syscall component is replaced by the full-code/WRITE-read wrapper;
host components are appended. State chronology projects independently of their Memory effects.
Auxiliary Byte requirements and State silence are static component-interface obligations.
Complete host execution, source-record authentication, and outgoing Memory currency remain open.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def tables (image : ProgramImage) (source : ExecutionSnapshot) (auxiliary : List (Component (ZMod p))) :=
  (ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer ++ auxiliary

def ensemble (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source auxiliary
  channels := HostCallChip.channel.toRaw :: (ProtectedLocalCore.ensemble image source).channels ++ channels
  verifier := LocalCore.verifier image source
  verifier_length_zero := by intros; rfl

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) (auxiliary : List (Component (ZMod p))) :
    (tables image source auxiliary).length = 60 + auxiliary.length := by
  simp only [tables, List.length_append, List.length_set, ProtectedLocalCore.tables_length]

theorem core_component (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 59) :
    (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega) =
      if 58 = index.val then HostCallLedger.producer else
        (ProtectedLocalCore.tables image source)[index.val]'(by rw [ProtectedLocalCore.tables_length]; omega) := by
  simp only [tables]
  rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.getElem_set]

omit [Fact (2 ^ 25 < p)] in
private theorem unchanged_projection (original extended : Component (ZMod p))
    (assertions : extended.operations.constraints = original.operations.constraints)
    (lookups : extended.operations.lookups = original.operations.lookups)
    (byte : extended.operations.interactionsWith byteChannel.toRaw = original.operations.interactionsWith byteChannel.toRaw)
    (state : extended.operations.interactionsWith stateChannel.toRaw = original.operations.interactionsWith stateChannel.toRaw) :
    (∀ env, extended.operations.ConstraintsHold env → original.operations.ConstraintsHold env) ∧
    (∀ env, extended.operations.ChannelGuarantees byteChannel.toRaw env → original.operations.ChannelGuarantees byteChannel.toRaw env) ∧
      original.operations.interactionsWith stateChannel.toRaw = extended.operations.interactionsWith stateChannel.toRaw := by
  refine ⟨?_, ?_, state.symm⟩
  · intro env checked
    simpa only [Operations.ConstraintsHold, assertions, lookups] using checked
  · intro env guarantees
    exact Operations.channelGuarantees_of_interactionsWith_subset _ _ _ (byte ▸ List.Subset.refl _) env guarantees

/-- Every retained component projects its constraints, Byte guarantees, and complete State ledger. -/
theorem component_projection (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 59) :
    let extended := (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)
    let original := (LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)
    (∀ env, extended.operations.ConstraintsHold env → original.operations.ConstraintsHold env) ∧
    (∀ env, extended.operations.ChannelGuarantees byteChannel.toRaw env → original.operations.ChannelGuarantees byteChannel.toRaw env) ∧
      original.operations.interactionsWith stateChannel.toRaw = extended.operations.interactionsWith stateChannel.toRaw := by
  dsimp only
  rw [core_component]
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by decide⟩ := Fin.ext wrapper.symm
    subst index
    simp only [↓reduceIte]
    exact ⟨HostCallProjection.constraints_original, HostCallProjection.byte_guarantees,
      HostCallProjection.state_interactions⟩
  · rw [if_neg wrapper]
    have old := ProtectedLocalCore.component_projection (p := p) image source index
    exact unchanged_projection _ _ old.1 old.2.1
      (old.2.2 _ (by simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw]))
      (old.2.2 _ (by simp [stateChannel, WritePermissionProvider.channel, Channel.toRaw]))

/-- Host tables can add arbitrary Memory effects. Their Byte requirements must follow locally,
and they do not contribute CPU State edges. These are static circuit-interface properties. -/
structure AuxiliaryInterface (auxiliary : List (Component (ZMod p))) : Prop where
  byte : ∀ component ∈ auxiliary, ∀ env, component.operations.ConstraintsHold env →
    component.operations.ChannelRequirements byteChannel.toRaw env
  state : ∀ component ∈ auxiliary, stateChannel.toRaw ∉ component.circuit.channels

omit [Fact (2 ^ 25 < p)] in
/-- Static channel interfaces compose over appended physical component blocks. -/
theorem AuxiliaryInterface.append {left right : List (Component (ZMod p))}
    (first : AuxiliaryInterface left) (second : AuxiliaryInterface right) :
    AuxiliaryInterface (left ++ right) := by
  constructor
  · intro component member env checked
    rcases List.mem_append.mp member with member | member
    · exact first.byte component member env checked
    · exact second.byte component member env checked
  · intro component member
    rcases List.mem_append.mp member with member | member
    · exact first.state component member
    · exact second.state component member

omit [Fact (2 ^ 25 < p)] in
/-- Restriction and reordering preserve a component-local interface. -/
theorem AuxiliaryInterface.of_subset {left right : List (Component (ZMod p))}
    (interface : AuxiliaryInterface right) (subset : left ⊆ right) : AuxiliaryInterface left :=
  ⟨fun component member => interface.byte component (subset member),
    fun component member => interface.state component (subset member)⟩

omit [Fact (2 ^ 25 < p)] in
/-- Most host components only consume Byte checks; their declared interfaces suffice. -/
theorem AuxiliaryInterface.of_channels (auxiliary : List (Component (ZMod p)))
    (byte : ∀ component ∈ auxiliary, byteChannel.toRaw ∉ component.circuit.channelsWithRequirements)
    (state : ∀ component ∈ auxiliary, stateChannel.toRaw ∉ component.circuit.channels) :
    AuxiliaryInterface auxiliary := by
  refine ⟨?_, state⟩
  intro component member env constraints
  exact Operations.requirements_of_not_mem _ _ _
    (component.inChannelsOrRequirements_of_constraints env constraints) _ (byte component member)

private theorem protected_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ ProtectedLocalCore.tables image source)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  have limit : index < 60 := by simpa only [ProtectedLocalCore.tables_length] using bound
  by_cases core : index < 59
  · have projection := ProtectedLocalCore.component_projection (p := p) image source ⟨index, core⟩
    have original := LocalCore.component_byte_requirements image source
      ((LocalCore.tables image source)[index]'(by rw [LocalCore.tables_length]; exact core))
      (List.mem_cons_of_mem _ (List.getElem_mem _)) env (by
        simpa only [Operations.ConstraintsHold, projection.1, projection.2.1] using constraints)
    apply Operations.channelRequirements_of_interactionsWith_subset _ _ _ ?_ env original
    rw [projection.2.2 byteChannel.toRaw (by simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw])]
    exact List.Subset.refl _
  · have last : index = 59 := by omega
    subst index
    apply Operations.requirements_of_not_mem _ _ _
      (((ProtectedLocalCore.tables image source)[59]).inChannelsOrRequirements_of_constraints env constraints)
    change byteChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
    simp [byteChannel, WritePermissionProvider.channel, Channel.toRaw]

/-- Every Byte provider in the extended assembly proves its own local requirement. -/
theorem component_byte_requirements (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (interface : AuxiliaryInterface auxiliary) (component : Component (ZMod p))
    (member : component ∈ (ensemble image source auxiliary channels).allTables)
    (env : Environment (ZMod p)) (constraints : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  simp only [Ensemble.allTables, ensemble, List.mem_cons] at member
  rcases member with rfl | member
  · exact LocalCore.component_byte_requirements image source _ (List.mem_cons_self ..) env constraints
  · rcases List.mem_append.mp member with core | extra
    · rcases List.mem_or_eq_of_mem_set core with original | rfl
      · exact protected_byte_requirements image source component original env constraints
      · apply Operations.requirements_of_not_mem _ _ _
          (HostCallLedger.producer.inChannelsOrRequirements_of_constraints env constraints)
        change byteChannel.toRaw ∉ [memoryChannel.toRaw, HostCallChip.channel.toRaw]
        simp [byteChannel, memoryChannel, HostCallChip.channel, Channel.toRaw]
    · exact interface.byte component extra env constraints

private theorem projectionLength (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p))) :
    (LocalCore.ensemble (p := p) image source).tables.length ≤
      (ensemble image source auxiliary channels).tables.length := by
  change (LocalCore.tables (p := p) image source).length ≤ (tables image source auxiliary).length
  rw [LocalCore.tables_length, tables_length]
  omega

/-- The chronology projection retains physical arrays, data, public input, and the full source. -/
def localWitness {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    EnsembleWitness (LocalCore.ensemble (p := p) image source) :=
  witness.project (LocalCore.ensemble image source) (projectionLength image source auxiliary channels)

theorem localWitness_constraints {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints) : (localWitness witness).Constraints := by
  apply witness.project_constraints_of (target := LocalCore.ensemble image source)
    (projectionLength image source auxiliary channels) rfl ?_ constraints
  intro index
  exact (component_projection image source auxiliary ⟨index.val, by
    simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).1

theorem localWitness_byte {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel byteChannel.toRaw) :
    ∀ table ∈ (localWitness witness).allTables, table.ChannelGuarantees byteChannel.toRaw := by
  have byte := witness.channelGuarantees_of_component_requirements byteChannel.toRaw constraints balanced
    (component_byte_requirements image source auxiliary channels interface)
  apply witness.project_channelGuarantees_of (target := LocalCore.ensemble image source)
    (projectionLength image source auxiliary channels) rfl byteChannel.toRaw ?_ byte
  intro index
  exact (component_projection image source auxiliary ⟨index.val, by
    simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).2.1

private theorem suffix_components (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) :
    (tables image source auxiliary).drop 59 = ⟨WritePermissionProvider.circuit image⟩ :: auxiliary := by
  have suffix : (ProtectedLocalCore.tables (p := p) image source).drop 59 =
      [⟨WritePermissionProvider.circuit image⟩] := by
    rw [ProtectedLocalCore.tables, List.drop_left' (by
      simp only [List.length_set, LocalCore.tables_length])]
  rw [tables, List.drop_append_of_le_length (by
    simp only [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.drop_set_of_lt (by decide), suffix]
  rfl

/-- Host effects do not erase, duplicate, or add any CPU State edge. -/
theorem localWitness_state {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (interface : AuxiliaryInterface auxiliary) :
    (localWitness witness).interactionsWith stateChannel.toRaw = witness.interactionsWith stateChannel.toRaw := by
  apply witness.project_interactions (target := LocalCore.ensemble image source)
    (projectionLength image source auxiliary channels) rfl stateChannel.toRaw ?_ ?_
  · intro index
    exact (component_projection image source auxiliary ⟨index.val, by
      simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩).2.2
  · change (witness.tables.drop (LocalCore.tables image source).length).flatMap _ = []
    rw [LocalCore.tables_length]
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_drop, witness.tables_map_component] at mapped
    change table.component ∈ (tables image source auxiliary).drop 59 at mapped
    rw [suffix_components] at mapped
    apply table.interactionsWith_nil_of_channel_not_mem
    rcases List.mem_cons.mp mapped with same | extra
    · rw [same]
      change stateChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
      simp [stateChannel, WritePermissionProvider.channel, Channel.toRaw]
    · exact interface.state table.component extra

private theorem component_other_interactions (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (index : Fin 59) (channel : RawChannel (ZMod p))
    (notByte : channel ≠ byteChannel.toRaw) (notMemory : channel ≠ memoryChannel.toRaw)
    (notCall : channel ≠ HostCallChip.channel.toRaw) (notPermission : channel ≠ WritePermissionProvider.channel.toRaw) :
    ((LocalCore.tables (p := p) image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)).operations.interactionsWith channel =
      ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).operations.interactionsWith channel := by
  rw [core_component]
  by_cases wrapper : 58 = index.val
  · have same : index = ⟨58, by decide⟩ := Fin.ext wrapper.symm
    subst index
    simp only [↓reduceIte]
    exact HostCallProjection.other_interactions channel notByte notMemory notCall
  · rw [if_neg wrapper]
    exact ((ProtectedLocalCore.component_projection (p := p) image source index).2.2 channel notPermission).symm

/-- Channels untouched by the host wrappers retain their complete ledger when the appended
components are silent. This includes Program and both private Memory-boundary ordering channels. -/
theorem localWitness_other {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (channel : RawChannel (ZMod p))
    (notByte : channel ≠ byteChannel.toRaw) (notMemory : channel ≠ memoryChannel.toRaw)
    (notCall : channel ≠ HostCallChip.channel.toRaw) (notPermission : channel ≠ WritePermissionProvider.channel.toRaw)
    (silent : ∀ component ∈ auxiliary, channel ∉ component.circuit.channels) :
    (localWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  apply witness.project_interactions (target := LocalCore.ensemble image source)
    (projectionLength image source auxiliary channels) rfl channel ?_ ?_
  · intro index
    exact component_other_interactions image source auxiliary ⟨index.val, by
      simpa only [LocalCore.ensemble, LocalCore.tables_length] using index.isLt⟩ channel
      notByte notMemory notCall notPermission
  · change (witness.tables.drop (LocalCore.tables image source).length).flatMap _ = []
    rw [LocalCore.tables_length]
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_drop, witness.tables_map_component] at mapped
    change table.component ∈ (tables image source auxiliary).drop 59 at mapped
    rw [suffix_components] at mapped
    apply table.interactionsWith_nil_of_channel_not_mem
    rcases List.mem_cons.mp mapped with same | extra
    · rw [same]
      change channel ∉ [WritePermissionProvider.channel.toRaw]
      simpa only [List.mem_singleton] using notPermission
    · exact silent table.component extra

/-- The full Program ledger survives projection when host auxiliaries do not emit fetches.
This preserves its count bound without projecting the extended Byte or Memory balance. -/
theorem localWitness_program {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels) :
    (localWitness witness).interactionsWith programChannel.toRaw = witness.interactionsWith programChannel.toRaw :=
  localWitness_other witness programChannel.toRaw
    (by simp [programChannel, byteChannel, Channel.toRaw])
    (by simp [programChannel, memoryChannel, Channel.toRaw])
    (by simp [programChannel, HostCallChip.channel, Channel.toRaw])
    (by simp [programChannel, WritePermissionProvider.channel, Channel.toRaw]) silent

/-- Raw constraints and the extended ensemble's own balance supply exactly the facts chronology uses. -/
theorem orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) : LocalCore.OrderingChannels (localWitness witness) := by
  refine ⟨localWitness_byte witness interface constraints (balanced _ ?_), ?_⟩
  · simp [ensemble, ProtectedLocalCore.ensemble, LocalCore.ensemble, sp1Ensemble_channels]
  · change BalancedInteractions ((localWitness witness).interactionsWith stateChannel.toRaw)
    rw [localWitness_state witness interface]
    exact balanced _ (by simp [ensemble, ProtectedLocalCore.ensemble, LocalCore.ensemble, sp1Ensemble_channels])

/-- An exhaustive CPU walk between the shard's actual public endpoints, with every host-call
instruction retained. Full Memory balance stays in the extended ensemble. -/
theorem executionRows_ordered {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ∃ ordered : List (NativeCore.ExecutionRow p), ordered.Perm (LocalCore.executionRows (localWitness witness)) ∧
      Walk.IsWalk (NativeCore.ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered :=
  LocalCore.executionRows_ordered_of_orderingChannels (localWitness witness)
    (localWitness_constraints witness constraints) (orderingChannels witness interface constraints balanced)

/-- The installed syscall wrapper's actual physical table. -/
def hostCallTable {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels)) : Table (ZMod p) :=
  witness.tables[58]'(by
    rw [← witness.same_length]
    change 58 < (tables image source auxiliary).length
    rw [tables_length]
    omega)

theorem hostCallTable_component {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (hostCallTable witness).component = HostCallLedger.producer := by
  rw [hostCallTable, ← witness.same_circuits]
  exact (core_component image source auxiliary ⟨58, by decide⟩).trans (if_pos rfl)

theorem hostCallTable_mem {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    hostCallTable witness ∈ witness.allTables :=
  witness.mem_allTables_of_mem_tables (List.getElem_mem _)

/-- The active instruction inventory is derived from the same physical rows, including padding. -/
theorem hostCallTable_projection {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    ((HostCallLedger.activeRows (hostCallTable witness)).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (LocalCore.systemTable (localWitness witness) 3) syscallInstrsRow (·.is_real) := by
  have table := witness.project_getElem (target := LocalCore.ensemble image source)
    (projectionLength image source auxiliary channels)
    ⟨58, by change 58 < (LocalCore.tables image source).length; rw [LocalCore.tables_length]; decide⟩
  change LocalCore.systemTable (localWitness witness) 3 =
    (hostCallTable witness).withComponent HostCallProjection.original at table
  rw [table]
  simp only [HostCallLedger.activeRows, List.filter_map, List.map_map, Function.comp_def,
    activeSystemRows, Table.withComponent, syscallInstrsRow, HostCallProjection.input_original,
    HostCallProjection.original, Component.rowInput]
  rfl

/-- Distinct clocks for actual wrapper calls follow from the extended AIR's own constraints and balance. -/
theorem hostCalls_clocks_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (interface : AuxiliaryInterface auxiliary) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ((HostCallLedger.calls (hostCallTable witness)).map HostCallLedger.clock).Nodup :=
  LocalCore.hostCalls_clocks_nodup_of_orderingChannels (localWitness witness)
    (localWitness_constraints witness constraints) (orderingChannels witness interface constraints balanced)
    (hostCallTable witness) (hostCallTable_projection witness)

end SP1Clean.Soundness.HostLocalCore
