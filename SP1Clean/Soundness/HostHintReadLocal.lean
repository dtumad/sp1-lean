import SP1Clean.Soundness.HostHintReadHandoff

/-! # HINT_READ cursor accounting in the installed local AIR

The handler and both physical word variants have fixed registered positions. Other handlers
and auxiliary resources may participate in queue, permission, Memory, and host protocols, but
are statically silent on this private word cursor. The extended ensemble's own balance then
supplies the shared cursor ledger and every selected call's balance. Queue authentication and
Memory currency remain separate semantic obligations.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Model.Core HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

abbrev ensemble (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) :=
  HostLocalHandoff.ensemble image source (receiver :: others) (wordResources ++ resources)
    ((HintReadWordChip.stateChannel.toRaw ::
      ((receiver (p := p) :: others).map (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
        (wordResources (p := p) ++ resources)).flatMap
          (fun component : Component (ZMod p) => component.circuit.channels)) ++ channels)

/-- Every channel used by an installed host component is included in full ensemble balance. -/
theorem auxiliary_channel_registered (image : ProgramImage) (source : ExecutionSnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) (component : Component (ZMod p))
    (member : component ∈ (receiver :: others).map (·.component) ++ (wordResources ++ resources))
    (channel : RawChannel (ZMod p)) (used : channel ∈ component.circuit.channels) :
    channel ∈ (ensemble image source others resources channels).channels := by
  exact List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨component, member, used⟩))))

/-- Static interfaces of the extension, independent of any witness or execution. -/
structure ExtensionInterface (others : List (HostLocalHandoff.Receiver (p := p)))
    (resources : List (Component (ZMod p))) : Prop where
  chronology : HostLocalCore.AuxiliaryInterface (others.map (·.component) ++ resources)
  hostCall : ∀ component ∈ resources, HostCallChip.channel.toRaw ∉ component.circuit.channels
  cursor : ∀ component ∈ others.map (·.component) ++ resources,
    HintReadWordChip.stateChannel.toRaw ∉ component.circuit.channels

/-- The currently implemented control, commitment, and HINT_LEN handlers need no cursor premise. -/
theorem availableInterface : ExtensionInterface (HostCallReceivers.available (p := p)) [] := by
  refine ⟨?_, by simp, ?_⟩
  · simpa only [List.append_nil] using HostCallReceivers.auxiliaryInterface (p := p)
  · have checked : ((HostCallReceivers.available (p := p)).map (·.component)).all (fun component =>
        !(component.circuit.channels.map RawChannel.name).contains
          (HintReadWordChip.stateChannel (p := p)).toRaw.name) = true := rfl
    intro component member used
    rw [List.append_nil] at member
    have valid := List.all_eq_true.mp checked component member
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at valid
    contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- HINT_READ contributes its already-proved static chronology interface. -/
theorem auxiliaryInterface (interface : ExtensionInterface others resources) :
    HostLocalCore.AuxiliaryInterface ((receiver :: others).map (·.component) ++ (wordResources ++ resources)) := by
  have member_split (component : Component (ZMod p))
      (member : component ∈ (receiver :: others).map (·.component) ++ (wordResources ++ resources)) :
      component ∈ [HostHintReadCoverage.handler, (HintReadCoverage.view false).component,
        (HintReadCoverage.view true).component] ∨ component ∈ others.map (·.component) ++ resources := by
    simpa only [List.map_cons, List.mem_append, List.mem_cons, wordResources, receiver,
      List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using member
  constructor
  · intro component member env constraints
    rcases member_split component member with hint | extra
    · exact HostHintReadHandoff.auxiliaryInterface.byte component hint env constraints
    · exact interface.chronology.byte component extra env constraints
  · intro component member
    rcases member_split component member with hint | extra
    · exact HostHintReadHandoff.auxiliaryInterface.state component hint
    · exact interface.chronology.state component extra

theorem resources_hostCall_silent (interface : ExtensionInterface others resources) :
    ∀ component ∈ wordResources (p := p) ++ resources,
      HostCallChip.channel.toRaw ∉ component.circuit.channels := by
  intro component member
  rcases List.mem_append.mp member with word | extra
  · exact wordResources_hostCall_silent component word
  · exact interface.hostCall component extra

/-- The registered handler retains its original physical rows and environment. -/
def handlerTable (witness : EnsembleWitness (ensemble image source others resources channels)) :=
  HostLocalHandoff.receiverTable witness ⟨0, by simp⟩

def wordTables (witness : EnsembleWitness (ensemble image source others resources channels)) :=
  (HostLocalHandoff.resourceTables witness).take 2

theorem handlerTable_component (witness : EnsembleWitness (ensemble image source others resources channels)) :
    (handlerTable witness).component = HostHintReadCoverage.handler := by
  rw [handlerTable, HostLocalHandoff.receiverTable_component]
  rfl

theorem wordTables_mem (witness : EnsembleWitness (ensemble image source others resources channels))
    (table : Table (ZMod p)) (member : table ∈ wordTables witness) : table ∈ witness.allTables := by
  apply witness.mem_allTables_of_mem_tables
  exact List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take member))

/-- The word-table identities and order follow from the actual resource registration. -/
theorem wordTables_components (witness : EnsembleWitness (ensemble image source others resources channels)) :
    (wordTables witness).map (·.component) = wordResources := by
  simp only [wordTables, List.map_take, HostLocalHandoff.resourceTables_components,
    wordResources, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]

theorem wordTables_aligned (witness : EnsembleWitness (ensemble image source others resources channels)) :
    List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants (wordTables witness) := by
  have equal : List.Forall₂ (· = ·)
      (HintReadCoverage.variants.map fun last => (HintReadCoverage.view (p := p) last).component)
      ((wordTables witness).map (·.component)) := by
    rw [List.forall₂_eq_eq_eq, wordTables_components]
    rfl
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using equal

private theorem cursor_fresh : HintReadWordChip.stateChannel.toRaw ∉
    (LocalCore.ensemble (p := p) image source).channels := by
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change false = true at present
  contradiction

private theorem wrapper_cursor_silent : HintReadWordChip.stateChannel.toRaw ∉
    (HostCallLedger.producer (p := p)).circuit.channels := by
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change false = true at present
  contradiction

/-- Only the actual HINT_READ handler and its two word tables contribute to this private cursor. -/
theorem cursor_interactions (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) :
    witness.interactionsWith HintReadWordChip.stateChannel.toRaw =
      (handlerTable witness).interactionsWith HintReadWordChip.stateChannel.toRaw ++
        (wordTables witness).flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw) := by
  rw [HostLocalCore.interactions_split_new witness _ cursor_fresh (by
    intro same
    have names := congrArg RawChannel.name same
    simp [HintReadWordChip.stateChannel, WritePermissionProvider.channel, Channel.toRaw] at names)]
  have wrapper : (HostLocalCore.hostCallTable witness).interactionsWith HintReadWordChip.stateChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    exact wrapper_cursor_silent
  rw [wrapper, List.nil_append]
  have split : HostLocalHandoff.receiverTables witness ++ HostLocalHandoff.resourceTables witness =
      HostLocalCore.auxiliaryTables witness := List.take_append_drop _ _
  have receiverSplit : HostLocalHandoff.receiverTables witness =
      handlerTable witness :: (HostLocalHandoff.receiverTables witness).drop 1 := by
    have bound := (HostLocalHandoff.receiverTables_aligned witness).length_eq
    change (receiver :: others).length = (HostLocalHandoff.receiverTables witness).length at bound
    exact (List.cons_getElem_drop_succ (l := HostLocalHandoff.receiverTables witness) (n := 0) (h := by simp only [List.length_cons] at bound; omega)).symm
  have receiverSilent : ((HostLocalHandoff.receiverTables witness).drop 1).flatMap
      (·.interactionsWith HintReadWordChip.stateChannel.toRaw) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    apply interface.cursor table.component
    apply List.mem_append_left
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    simpa only [List.map_drop, HostLocalHandoff.receiverTables_components, List.map_cons,
      List.drop_succ_cons, List.drop_zero] using mapped
  have resourceSilent : ((HostLocalHandoff.resourceTables witness).drop 2).flatMap
      (·.interactionsWith HintReadWordChip.stateChannel.toRaw) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    apply interface.cursor table.component
    apply List.mem_append_right
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    simpa only [List.map_drop, HostLocalHandoff.resourceTables_components, wordResources,
      List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero] using mapped
  rw [← split, List.flatMap_append, receiverSplit, List.flatMap_cons, receiverSilent, List.append_nil]
  congr 1
  have resourceSplit := List.take_append_drop 2 (HostLocalHandoff.resourceTables witness)
  rw [← resourceSplit, List.flatMap_append, resourceSilent, List.append_nil]
  rfl

/-- Shared cursor balance comes from the extended ensemble's own balanced channel. -/
theorem cursor_balanced (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (balanced : witness.BalancedChannels) :
    BalancedInteractions
      ((handlerTable witness).interactionsWith HintReadWordChip.stateChannel.toRaw ++
        (wordTables witness).flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)) := by
  rw [← cursor_interactions witness interface]
  apply balanced
  simp [ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble]

/-- Complete HostCall accounting and CPU chronology supply distinct physical handler clocks. -/
theorem handler_clocks_nodup (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) :
    (((handlerTable witness).table.map (handlerTable witness).environment).map
      HostHintReadPartition.callClock).Nodup :=
  handler_clocks_nodup_of_registered witness (auxiliaryInterface interface)
    (resources_hostCall_silent interface) constraints balanced ⟨0, by simp⟩ rfl

/-- No supplied handler ledger, word-table alignment, uniqueness, or per-call balance is needed. -/
theorem balanced_for (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment) :
    BalancedInteractions
      (HostHintReadCoverage.handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) (wordTables witness)).flatMap
          (·.interactionsWith HintReadWordChip.stateChannel.toRaw)) :=
  HostHintReadPartition.balanced_for (handlerTable witness) (handlerTable_component witness)
    (wordTables witness) (wordTables_aligned witness) env member
    (handler_clocks_nodup witness interface constraints balanced) (cursor_balanced witness interface balanced)

/-- An installed consumer cannot belong to a call absent from the physical handler table.
Authenticated word-step contracts suffice; prior Memory values and timestamps are separate. -/
theorem consumer_has_handler (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (balanced : witness.BalancedChannels)
    (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) :
    ∃ env ∈ (handlerTable witness).table.map (handlerTable witness).environment,
      HostHintReadPartition.callClock env = HostHintReadPartition.clock (HintReadCoverage.rowInput row).previous :=
  HostHintReadPartition.consumer_has_handler (handlerTable witness) (handlerTable_component witness)
    (wordTables witness) (wordTables_aligned witness) wordSpecs (cursor_balanced witness interface balanced) row member


end SP1Clean.Soundness.HostHintReadLocal
