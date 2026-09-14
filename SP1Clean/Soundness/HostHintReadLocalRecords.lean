import SP1Clean.Soundness.HostHintRecordSources
import SP1Clean.Soundness.HostLocalCoreAuthentication

/-! # Record authentication in the installed HINT_READ assembly

The retained core is silent on immutable hint records. The handler, word consumers, and existing
non-RAM handlers cannot create records. Fixed source components establish their own contracts;
future allocation providers must prove the same source interface. Actual whole-witness balance
therefore establishes both local channel guarantees and immutable contents for every requested
record. The store here may include future allocations; `HostHintReadLocalExecution` restricts
bindings to the current frontier using current-head truth and the actual cursor path.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintReadHandoff HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

theorem auxiliary_record_sources (store : Store)
    (sources : ∀ component ∈ others.map (·.component) ++ resources,
      HostHintRecordSources.Authenticates store component) :
    ∀ component ∈ (receiver :: others).map (·.component) ++ (wordResources ++ resources),
      HostHintRecordSources.Authenticates store component := by
  intro component member
  simp only [List.map_cons, List.mem_append, List.mem_cons, wordResources, receiver,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | other) | ((rfl | rfl) | extra)
  · exact HostHintRecordSources.handler_authenticates store
  · exact sources component (List.mem_append_left _ other)
  · exact HostHintRecordSources.word_consumer_authenticates store false
  · exact HostHintRecordSources.word_consumer_authenticates store true
  · exact sources component (List.mem_append_right _ extra)

private theorem node_fresh : nodeChannel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  change false = true at present
  contradiction

private theorem word_fresh : wordChannel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  change false = true at present
  contradiction

/-- Actual source rows authenticate immutable contents. Dynamic allocations may establish this
after grounding their inputs; fixed providers derive it directly from local constraints. -/
def RecordAuthentication (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) : Prop :=
  ∀ table ∈ HostLocalCore.auxiliaryTables witness,
    table.Authenticates nodeChannel (fun record => record.Valid ∧ record.Binds store) ∧
    table.Authenticates wordChannel (fun record => record.Valid ∧ record.Binds store)

theorem record_authentication_of_components
    (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) (sources : ∀ component ∈ others.map (·.component) ++ resources,
      HostHintRecordSources.Authenticates store component)
    (constraints : witness.Constraints) : RecordAuthentication witness store := by
  intro table member
  have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [HostLocalCore.auxiliaryTables_components] at component
  have source := auxiliary_record_sources store sources table.component component
  have checked := constraints table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop member))
  exact ⟨Table.Authenticates.of_component table _ _ source.node checked,
    Table.Authenticates.of_component table _ _ source.word checked⟩

theorem node_authenticated (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) (authenticated : RecordAuthentication witness store)
    (balanced : witness.BalancedChannels) (record : NodeRecord (ZMod p))
    (member : nodeChannel.pulledValue record ∈ witness.interactionsWith nodeChannel.toRaw) :
    record.Valid ∧ record.Binds store := by
  apply HostLocalCore.authenticated_auxiliary_pull witness nodeChannel node_fresh
    (by simp [nodeChannel, WritePermissionProvider.channel, Channel.toRaw]) ?_
    (fun record => record.Valid ∧ record.Binds store)
    (fun table member => (authenticated table member).1) (balanced _ ?_) record member
  · intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at present
    contradiction
  · apply auxiliary_channel_registered image source others resources channels HostHintReadCoverage.handler
      (by simp [receiver]) nodeChannel.toRaw
    simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]

theorem word_authenticated (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) (authenticated : RecordAuthentication witness store)
    (balanced : witness.BalancedChannels) (record : WordRecord (ZMod p))
    (member : wordChannel.pulledValue record ∈ witness.interactionsWith wordChannel.toRaw) :
    record.Valid ∧ record.Binds store := by
  apply HostLocalCore.authenticated_auxiliary_pull witness wordChannel word_fresh
    (by simp [wordChannel, WritePermissionProvider.channel, Channel.toRaw]) ?_
    (fun record => record.Valid ∧ record.Binds store)
    (fun table member => (authenticated table member).2) (balanced _ ?_) record member
  · intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at present
    contradiction
  · apply auxiliary_channel_registered image source others resources channels HostHintReadCoverage.handler
      (by simp [receiver]) wordChannel.toRaw
    simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]

theorem node_guarantees (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) (authenticated : RecordAuthentication witness store)
    (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees nodeChannel.toRaw :=
  witness.channelGuarantees_of_authenticated_pulls nodeChannel
    (fun record member => (node_authenticated witness store authenticated balanced record member).1)

theorem word_guarantees (witness : EnsembleWitness (ensemble image source others resources channels))
    (store : Store) (authenticated : RecordAuthentication witness store)
    (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees wordChannel.toRaw :=
  witness.channelGuarantees_of_authenticated_pulls wordChannel
    (fun record member => (word_authenticated witness store authenticated balanced record member).1)

private theorem handler_spec_of_channels (env : Environment (ZMod p))
    (constraints : (HostHintReadCoverage.handler (p := p)).operations.ConstraintsHold env)
    (bytes : HostHintReadCoverage.handler.operations.ChannelGuarantees Channels.byteChannel.toRaw env)
    (nodes : HostHintReadCoverage.handler.operations.ChannelGuarantees nodeChannel.toRaw env)
    (words : HostHintReadCoverage.handler.operations.ChannelGuarantees wordChannel.toRaw env) :
    HostHintReadCoverage.handler.Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (HostHintReadCoverage.handler.inChannelsOrGuarantees env)]
  intro channel member
  change channel ∈ [Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, wordChannel.toRaw,
    Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, nodeChannel.toRaw,
    HostCallChip.channel.toRaw, stateChannel.toRaw, HintReadWordChip.stateChannel.toRaw] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytes
    | exact nodes
    | exact words
    | exact Operations.channelGuarantees_of_trivial _
        (by simp [HostCallChip.channel, stateChannel, HintReadWordChip.stateChannel, Channel.toRaw]) _ _

theorem handlerTable_mem (witness : EnsembleWitness (ensemble image source others resources channels)) :
    handlerTable witness ∈ witness.allTables := by
  apply witness.mem_allTables_of_mem_tables
  exact List.mem_of_mem_drop (List.mem_of_mem_take (List.getElem_mem _))

theorem byte_guarantees (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees Channels.byteChannel.toRaw := by
  apply witness.channelGuarantees_of_component_requirements Channels.byteChannel.toRaw constraints
    (balanced _ ?_) (HostLocalCore.component_byte_requirements image source _ _ (auxiliaryInterface interface))
  apply auxiliary_channel_registered image source others resources channels HostHintReadCoverage.handler
    (by simp [receiver]) Channels.byteChannel.toRaw
  exact List.mem_append_left _ (List.mem_cons_self ..)

/-- Handler row specifications follow from the installed AIR and its authenticated sources. -/
theorem handler_spec (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (store : Store)
    (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (handlerTable witness).Spec := by
  have member := handlerTable_mem witness
  have bytes := byte_guarantees witness interface constraints balanced _ member
  have nodes := node_guarantees witness store authenticated balanced _ member
  have words := word_guarantees witness store authenticated balanced _ member
  intro physical present
  have checked := constraints _ member physical present
  have byte := bytes physical present
  have node := nodes physical present
  have word := words physical present
  rw [handlerTable_component] at checked byte node word ⊢
  exact handler_spec_of_channels _ checked byte node word

private theorem word_spec_of_channels (last : Bool) (env : Environment (ZMod p))
    (constraints : (HintReadCoverage.view last).component.operations.ConstraintsHold env)
    (bytes : (HintReadCoverage.view last).component.operations.ChannelGuarantees Channels.byteChannel.toRaw env)
    (memory : (HintReadCoverage.view last).component.operations.ChannelGuarantees Channels.memoryChannel.toRaw env)
    (words : (HintReadCoverage.view last).component.operations.ChannelGuarantees wordChannel.toRaw env) :
    (HintReadCoverage.view last).component.Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ ((HintReadCoverage.view last).component.inChannelsOrGuarantees env)]
  intro channel member
  cases last
  all_goals
    change channel ∈ [Channels.byteChannel.toRaw, Channels.memoryChannel.toRaw, wordChannel.toRaw,
      Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, HostRamAccessChip.channel.toRaw,
      WritePermissionProvider.channel.toRaw, WritePermissionProvider.channel.toRaw,
      WritePermissionProvider.channel.toRaw, WritePermissionProvider.channel.toRaw,
      WritePermissionProvider.channel.toRaw, WritePermissionProvider.channel.toRaw,
      WritePermissionProvider.channel.toRaw, WritePermissionProvider.channel.toRaw,
      HintReadWordChip.stateChannel.toRaw] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytes
    | exact memory
    | exact words
    | exact Operations.channelGuarantees_of_trivial _
        (by simp [HostRamAccessChip.channel, WritePermissionProvider.channel,
          HintReadWordChip.stateChannel, Channel.toRaw]) _ _

/-- The word rows' remaining representation dependency is exactly their actual Memory guarantees.
Immutable words and Byte guarantees are derived from the installed sources and balance. -/
theorem word_spec (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (store : Store)
    (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memory : ∀ table ∈ wordTables witness, table.ChannelGuarantees Channels.memoryChannel.toRaw) :
    ∀ table ∈ wordTables witness, table.Spec := by
  intro table member
  have present := wordTables_mem witness table member
  have byte := byte_guarantees witness interface constraints balanced table present
  have word := word_guarantees witness store authenticated balanced table present
  have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [wordTables_components] at component
  simp only [wordResources, List.mem_cons, List.not_mem_nil, or_false] at component
  have checked := constraints table present
  have mem := memory table member
  rcases component with component | component
  all_goals
    intro physical physicalMem
    have checkedRow := checked physical physicalMem
    have byteRow := byte physical physicalMem
    have wordRow := word physical physicalMem
    have memoryRow := mem physical physicalMem
    rw [component] at checkedRow byteRow wordRow memoryRow ⊢
    exact word_spec_of_channels _ _ checkedRow byteRow memoryRow wordRow

/-- Both fixed record providers are computed from the source bytes. -/
def sourceResources (hints : List Bytes) : List (Component (ZMod p)) :=
  [⟨HostHintQueue.source hints⟩, ⟨HostHintQueue.sourceWord hints⟩]

/-- The existing handlers plus source providers need no caller-supplied record-source proof. -/
theorem source_record_sources (hints : List Bytes) (store : Store)
    (extension : Extends (ofList hints).1 store)
    (component : Component (ZMod p))
    (member : component ∈ (HostCallReceivers.available (p := p)).map (·.component) ++ sourceResources hints) :
    HostHintRecordSources.Authenticates store component := by
  rcases List.mem_append.mp member with handler | fixed
  · exact HostHintRecordSources.available_authenticates store component handler
  · simp only [sourceResources, List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    · exact (HostHintRecordSources.source_node_authenticates hints).extend extension
    · exact (HostHintRecordSources.source_word_authenticates hints).extend extension

/-- The fixed-source registration authenticates its actual records from the snapshot's hint bytes. -/
theorem source_record_authentication
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (store : Store) (extension : Extends (ofList source.host.io.hints).1 store)
    (constraints : witness.Constraints) : RecordAuthentication witness store :=
  record_authentication_of_components witness store
    (source_record_sources source.host.io.hints store extension) constraints

theorem source_interface (hints : List Bytes) :
    ExtensionInterface (HostCallReceivers.available (p := p)) (sourceResources hints) := by
  have sourceSilent (component : Component (ZMod p)) (member : component ∈ sourceResources hints)
      (channel : RawChannel (ZMod p)) (node : channel ≠ nodeChannel.toRaw) (word : channel ≠ wordChannel.toRaw) :
      channel ∉ component.circuit.channels := by
    simp only [sourceResources, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change channel ∉ [nodeChannel.toRaw]
      simpa only [List.mem_singleton] using node
    · change channel ∉ [wordChannel.toRaw]
      simpa only [List.mem_singleton] using word
  constructor
  · constructor
    · intro component member env checked
      rcases List.mem_append.mp member with handler | fixed
      · exact HostCallReceivers.auxiliaryInterface.byte component handler env checked
      · apply Operations.requirements_of_not_mem _ _ _
          (component.inChannelsOrRequirements_of_constraints env checked)
        intro used
        exact sourceSilent component fixed Channels.byteChannel.toRaw
          (by simp [Channels.byteChannel, nodeChannel, Channel.toRaw])
          (by simp [Channels.byteChannel, wordChannel, Channel.toRaw])
          (List.mem_append_right _ used)
    · intro component member
      rcases List.mem_append.mp member with handler | fixed
      · exact HostCallReceivers.auxiliaryInterface.state component handler
      · exact sourceSilent component fixed Channels.stateChannel.toRaw
          (by simp [Channels.stateChannel, nodeChannel, Channel.toRaw])
          (by simp [Channels.stateChannel, wordChannel, Channel.toRaw])
  · intro component member
    exact sourceSilent component member HostCallChip.channel.toRaw
      (by simp [HostCallChip.channel, nodeChannel, Channel.toRaw])
      (by simp [HostCallChip.channel, wordChannel, Channel.toRaw])
  · intro component member
    rcases List.mem_append.mp member with handler | fixed
    · exact availableInterface.cursor component (List.mem_append_left [] handler)
    · exact sourceSilent component fixed HintReadWordChip.stateChannel.toRaw
        (by simp [HintReadWordChip.stateChannel, nodeChannel, Channel.toRaw])
        (by simp [HintReadWordChip.stateChannel, wordChannel, Channel.toRaw])

end SP1Clean.Soundness.HostHintReadLocal
