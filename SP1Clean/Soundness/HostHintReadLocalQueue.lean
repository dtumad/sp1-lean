import SP1Clean.Soundness.HostHintReadLocalRecords
import SP1Clean.Soundness.HostQueueOrder

/-! # The complete installed queue-state ledger

HINT_READ and both HINT_LEN variants occupy fixed physical handler positions. The retained
core, other implemented handlers, and RAM word consumers are silent on queue state. Every
remaining contribution comes from the actual extra resource tables; these must eventually
implement authenticated endpoints and allocations. In particular the fixed node/word source
registration alone has no queue endpoints and admits no active queue-handler rows.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Model.Core HostHintQueue HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance queueClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance queueLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

/-- HINT_READ followed by the two HINT_LEN variants, in the actual receiver registry. -/
def queueTables (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :=
  handlerTable witness :: (HostLocalHandoff.receiverTables witness).drop 19

def extraTables (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :=
  (HostLocalHandoff.resourceTables witness).drop 2

theorem queueTables_components
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    (queueTables witness).map (·.component) = HostQueueOrder.indices.map (fun index => (HostQueueOrder.view index).component) := by
  simp only [queueTables, List.map_cons, handlerTable_component, List.map_drop,
    HostLocalHandoff.receiverTables_components]
  rfl

theorem queueTables_aligned
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    List.Forall₂ (fun index table => (HostQueueOrder.view index).component = table.component)
      HostQueueOrder.indices (queueTables witness) := by
  have same : List.Forall₂ (· = ·)
      (HostQueueOrder.indices.map fun index => (HostQueueOrder.view (p := p) index).component)
      ((queueTables witness).map (·.component)) := by
    rw [List.forall₂_eq_eq_eq, queueTables_components]
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using same

theorem queueTables_mem
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (table : Table (ZMod p)) (member : table ∈ queueTables witness) : table ∈ witness.allTables := by
  rcases List.mem_cons.mp member with rfl | member
  · exact handlerTable_mem witness
  · exact witness.mem_allTables_of_mem_tables
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_drop member)))

theorem extraTables_components
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    (extraTables witness).map (·.component) = resources := by
  simp only [extraTables, List.map_drop, HostLocalHandoff.resourceTables_components,
    wordResources, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

private theorem queue_fresh : stateChannel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  change false = true at present
  contradiction

private theorem wrapper_queue_silent : stateChannel.toRaw ∉ (HostCallLedger.producer (p := p)).circuit.channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  change false = true at present
  contradiction

private theorem control_queue_silent
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    (((HostLocalHandoff.receiverTables witness).drop 1).take 18).flatMap (·.interactionsWith stateChannel.toRaw) = [] := by
  have checked : (((HostCallReceivers.available (p := p)).map (·.component)).take 18).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains (stateChannel (p := p)).toRaw.name) = true := rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  simp only [List.map_take, List.map_drop, HostLocalHandoff.receiverTables_components,
    List.map_cons, List.drop_succ_cons, List.drop_zero] at mapped
  intro used
  have silent := List.all_eq_true.mp checked table.component mapped
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

private theorem word_queue_silent
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    (wordTables witness).flatMap (·.interactionsWith stateChannel.toRaw) = [] := by
  have checked : (wordResources (p := p)).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains (stateChannel (p := p)).toRaw.name) = true := rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [wordTables_components] at mapped
  intro used
  have silent := List.all_eq_true.mp checked table.component mapped
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

/-- This accounts for every installed table. No endpoint or future allocation contribution is dropped. -/
theorem queue_interactions
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels)) :
    witness.interactionsWith stateChannel.toRaw =
      (queueTables witness).flatMap (·.interactionsWith stateChannel.toRaw) ++
        (extraTables witness).flatMap (·.interactionsWith stateChannel.toRaw) := by
  rw [HostLocalCore.interactions_split_new witness _ queue_fresh
    (by simp [stateChannel, WritePermissionProvider.channel, Channel.toRaw])]
  have wrapper : (HostLocalCore.hostCallTable witness).interactionsWith stateChannel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    exact wrapper_queue_silent
  rw [wrapper, List.nil_append]
  have split : HostLocalHandoff.receiverTables witness ++ HostLocalHandoff.resourceTables witness =
      HostLocalCore.auxiliaryTables witness := List.take_append_drop _ _
  rw [← split, List.flatMap_append]
  have receivers : HostLocalHandoff.receiverTables witness =
      handlerTable witness :: (HostLocalHandoff.receiverTables witness).drop 1 := by
    have bound := (HostLocalHandoff.receiverTables_aligned witness).length_eq
    change (receiver :: HostCallReceivers.available).length = (HostLocalHandoff.receiverTables witness).length at bound
    exact (List.cons_getElem_drop_succ (l := HostLocalHandoff.receiverTables witness) (n := 0)
      (h := by simp only [List.length_cons] at bound; omega)).symm
  have controls := List.take_append_drop 18 ((HostLocalHandoff.receiverTables witness).drop 1)
  have words := List.take_append_drop 2 (HostLocalHandoff.resourceTables witness)
  rw [receivers, List.flatMap_cons, ← controls]
  simp only [List.flatMap_append, control_queue_silent, List.nil_append, List.drop_drop]
  rw [← words]
  simp only [List.flatMap_append]
  change _ ++ ((wordTables witness).flatMap (·.interactionsWith stateChannel.toRaw) ++
    (extraTables witness).flatMap (·.interactionsWith stateChannel.toRaw)) = _
  rw [word_queue_silent, List.nil_append]
  simp only [queueTables, List.flatMap_cons, extraTables, List.append_assoc]

/-- The installed AIR supplies all three queue-handler contracts without Memory assumptions. -/
theorem queue_specs
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources) (store : HintQueue.Store)
    (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ table ∈ queueTables witness, table.Spec := by
  intro table member
  have present := queueTables_mem witness table member
  rcases List.mem_cons.mp member with rfl | member
  · exact handler_spec witness interface store authenticated constraints balanced
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  simp only [List.map_drop, HostLocalHandoff.receiverTables_components] at mapped
  change table.component ∈ [⟨HostHintLengthChip.circuit false⟩, ⟨HostHintLengthChip.circuit true⟩] at mapped
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mapped
  have nodes := node_guarantees witness store authenticated balanced table present
  have checked := constraints table present
  rcases mapped with component | component
  all_goals
    intro physical physicalMem
    have rowChecked := checked physical physicalMem
    have rowNode := nodes physical physicalMem
    rw [component] at rowChecked rowNode ⊢
    exact HostHintLengthChip.component_spec_of_node _ _ rowChecked rowNode

/-- Once actual extra resources supply exactly the two queue endpoints, the installed AIR
orders every queue-handler occurrence. Endpoint authentication and construction remain explicit. -/
theorem queue_ordered_of_endpoints
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources) (store : HintQueue.Store)
    (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (initial final : State (ZMod p))
    (endpoints : (extraTables witness).flatMap (·.interactionsWith stateChannel.toRaw) =
      [stateChannel.pushedValue initial, stateChannel.pulledValue final]) :
    ∃ path : List (HostQueueOrder.Row (p := p)),
      path.Perm (TransitionView.readIndexedRows HostQueueOrder.indices (queueTables witness)) ∧
      Walk.IsWalk HostQueueOrder.edge initial final path := by
  have ledger := balanced stateChannel.toRaw (auxiliary_channel_registered image source HostCallReceivers.available
    resources channels HostHintReadCoverage.handler (by simp [receiver]) stateChannel.toRaw (by
      simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]))
  change BalancedInteractions (witness.interactionsWith stateChannel.toRaw) at ledger
  rw [queue_interactions, endpoints] at ledger
  exact HostQueueOrder.ordered _ (queueTables_aligned witness)
    (queue_specs witness interface store authenticated constraints balanced) initial final
    (balancedInteractions_of_perm ledger (List.perm_append_comm ..))

/-- If all extra resources are queue-silent, complete AIR balance forces every queue-handler
table empty. This diagnoses the missing queue endpoints in the fixed record-source assembly. -/
theorem queue_rows_nil_of_silent_resources
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources) (store : HintQueue.Store)
    (authenticated : RecordAuthentication witness store)
    (silent : ∀ component ∈ resources, stateChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    TransitionView.readIndexedRows HostQueueOrder.indices (queueTables witness) = [] := by
  have extra : (extraTables witness).flatMap (·.interactionsWith stateChannel.toRaw) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    apply silent table.component
    rw [← extraTables_components witness]
    exact List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  have ledger := balanced stateChannel.toRaw (auxiliary_channel_registered image source HostCallReceivers.available
    resources channels HostHintReadCoverage.handler (by simp [receiver]) stateChannel.toRaw (by
      simp [HostHintReadCoverage.handler, HostHintReadChip.circuit, circuit_norm]))
  change BalancedInteractions (witness.interactionsWith stateChannel.toRaw) at ledger
  rw [queue_interactions, extra, List.append_nil] at ledger
  exact HostQueueOrder.rows_nil_of_balanced _ (queueTables_aligned witness)
    (queue_specs witness interface store authenticated constraints balanced) ledger

/-- The fixed source registration lacks queue boundaries: all its queue handlers are necessarily
inactive under the full AIR relation, even though record-only regressions can contain active rows. -/
theorem source_queue_rows_nil
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    TransitionView.readIndexedRows HostQueueOrder.indices (queueTables witness) = [] := by
  apply queue_rows_nil_of_silent_resources witness (source_interface source.host.io.hints)
    (HintQueue.ofList source.host.io.hints).1
    (source_record_authentication witness _ (.refl _) constraints) _ constraints balanced
  intro component member used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  simp only [sourceResources, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> change false = true at present <;> contradiction

end SP1Clean.Soundness.HostHintReadLocal
