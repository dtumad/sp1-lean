import SP1Clean.Soundness.HostLocalCoreRows
import SP1Clean.Soundness.HostHintReadCPUMemory
import SP1Clean.Soundness.HostQueueCallProjection

/-! # CPU execution rows with their installed hint Memory effects

Each event keeps its State edge and fetch and adds the physical hint words assigned to it by
the two installed ledgers. The present source registry derives absence of WRITE, so its wrapper's
x12 pair is disabled; this is a proved property of that registry, not an inactivity premise or
a restriction on the eventual eight-call capstone. Future WRITE installation must retain that pair.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The original CPU event and its complete additional hint-word footprint. -/
noncomputable def eventFacts (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (event : ExecutionRow p) : RowFacts p :=
  { event.facts data with
    memPulls := (event.facts data).memPulls ++ (wordsAt data words event).map (fun row => (touch row).1)
    memPushes := (event.facts data).memPushes ++ (wordsAt data words event).map (fun row => (touch row).2) }

/-- Added Memory effects preserve the complete instruction State edge and committed fetch. -/
theorem eventFacts_state_fetch (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (event : ExecutionRow p) :
    (eventFacts data words event).statePull = (event.facts data).statePull ∧
      (eventFacts data words event).statePush = (event.facts data).statePush ∧
      (eventFacts data words event).fetch = (event.facts data).fetch := ⟨rfl, rfl, rfl⟩

/-- The enlarged execution rows add exactly their grouped words to both Memory aggregates. -/
theorem eventFacts_memory (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (cpu : List (ExecutionRow p)) (loc : MemLoc) :
    TimedGrounding.pushesAt (cpu.map (eventFacts data words)) loc =
        TimedGrounding.pushesAt (cpu.map (ExecutionRow.facts data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((cpu.flatMap (wordsAt data words)).map (fun row => (touch row).2)) : Multiset _) ∧
    TimedGrounding.pullsAt (cpu.map (eventFacts data words)) loc =
        TimedGrounding.pullsAt (cpu.map (ExecutionRow.facts data)) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((cpu.flatMap (wordsAt data words)).map (fun row => (touch row).1.1)) : Multiset _) := by
  constructor
  · have split := (List.flatMap_append_perm cpu (fun event => (event.facts data).memPushes)
      (fun event => (wordsAt data words event).map (fun row => (touch row).2))).symm
    have same := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
      (Multiset.coe_eq_coe.mpr split)
    simpa only [pushesAt_flatMap, List.flatMap_map, Function.comp_def, eventFacts, List.map_flatMap,
      filter_coe_append] using same
  · have split := (List.flatMap_append_perm cpu (fun event => (event.facts data).memPulls.map Prod.fst)
      (fun event => (wordsAt data words event).map (fun row => (touch row).1.1))).symm
    have same := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
      (Multiset.coe_eq_coe.mpr split)
    simpa only [pullsAt_flatMap, List.flatMap_map, Function.comp_def, eventFacts, List.map_append,
      List.map_map, List.map_flatMap, filter_coe_append] using same

private theorem unit_signs : signedVal (1 : ZMod p) = 1 ∧ signedVal (-1 : ZMod p) = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  constructor
  · rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  · rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num

/-- Both physical word variants emit exactly one prior and one pushed complete record. -/
theorem word_memory_messages (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) :
    producedMessages (tables.flatMap (typedTableInteractionsWith · memoryChannel)) =
        (TransitionView.readIndexedRows HintReadCoverage.variants tables).map (fun row => (touch row).2) ∧
      consumedMessages (tables.flatMap (typedTableInteractionsWith · memoryChannel)) =
        (TransitionView.readIndexedRows HintReadCoverage.variants tables).map (fun row => (touch row).1.1) := by
  have ledger : tables.flatMap (typedTableInteractionsWith · memoryChannel) =
      (TransitionView.readIndexedRows HintReadCoverage.variants tables).flatMap (fun row =>
        [TypedInteraction.pulledIfValue memoryChannel 1 (touch row).1.1,
         TypedInteraction.pushedIfValue memoryChannel 1 (touch row).2]) := by
    apply List.map_injective_iff.mpr TypedInteraction.raw_injective
    simp only [List.map_flatMap, typedTableInteractionsWith_raw, List.map_cons, List.map_nil,
      TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw, touch]
    exact HintReadWriteLedger.memory_ledger tables aligned
  rw [ledger, producedMessages_flatMap, consumedMessages_flatMap]
  simp [producedMessages, consumedMessages, unit_signs.1, unit_signs.2]
  exact ⟨List.flatMap_pure_eq_map _ _, List.flatMap_pure_eq_map _ _⟩

private theorem write_word_bits :
    Word.toBitVec64 (HostCallChip.writeWord (R := ZMod p)) = SyscallKind.write.code := by
  have two : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt
    (show 2 < p by have := Fact.out (p := 2 ^ 25 < p); omega)
  simp [HostCallChip.writeWord, Word.toBitVec64, Word.toNat, two, SyscallKind.code]

private theorem extra_disabled (input : HostCallChip.Inputs (ZMod p))
    (safe : Word.toBitVec64 (input.message (HostCallChip.writeFlag input.instruction.op_a_memory.prev_value)).code ≠
      SyscallKind.write.code) :
    (input.read (HostCallChip.writeFlag input.instruction.op_a_memory.prev_value)).is_real = 0 := by
  have different : input.instruction.op_a_memory.prev_value ≠ HostCallChip.writeWord := by
    intro same
    apply safe
    change Word.toBitVec64 input.instruction.op_a_memory.prev_value = _
    rw [same, write_word_bits]
  simp only [HostCallChip.Inputs.read, HostCallChip.writeFlag, if_neg different, mul_zero]

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

/-- The current physical receiver registry disables every x12 pair, including padding.
The general extended ledger still retains WRITE's pair when that handler is installed later. -/
theorem wrapper_disabled
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (specs : ∀ table ∈ queueTables witness, table.Spec) :
    ∀ env ∈ (HostLocalCore.hostCallTable witness).table.map (HostLocalCore.hostCallTable witness).environment,
      (HostCallProjection.extraRead env).is_real = 0 := by
  have calls := (HostQueueCallProjection.calls_projection witness interface constraints balanced specs).1
  have handoff := HostLocalHandoff.calls_perm witness (resources_hostCall_silent interface) constraints balanced
  intro env member
  have checked : HostCallLedger.producer.operations.ConstraintsHold env := by
    obtain ⟨physical, present, rfl⟩ := List.mem_map.mp member
    have checked := constraints _ (HostLocalCore.hostCallTable_mem witness) physical present
    rwa [HostLocalCore.hostCallTable_component] at checked
  rcases HostCallLedger.binary_of_constraints env checked with inactive | active
  · simp only [HostCallProjection.extraRead, HostCallChip.Inputs.read, inactive, zero_mul]
  · apply extra_disabled (HostCallLedger.input env)
    apply calls
    apply handoff.mem_iff.mp
    exact List.mem_map.mpr ⟨env, List.mem_filter.mpr ⟨member, decide_eq_true active⟩, rfl⟩

private theorem wrapper_messages_nil
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (disabled : ∀ env ∈ (HostLocalCore.hostCallTable witness).table.map (HostLocalCore.hostCallTable witness).environment,
      (HostCallProjection.extraRead env).is_real = 0) :
    producedMessages (HostLocalCore.wrapperMemory witness) = [] ∧
      consumedMessages (HostLocalCore.wrapperMemory witness) = [] := by
  have zero : signedVal (0 : ZMod p) = 0 := by simp [signedVal]
  rw [HostLocalCore.wrapperMemory, producedMessages_flatMap, consumedMessages_flatMap]
  constructor
  all_goals
    apply List.flatMap_eq_nil_iff.mpr
    intro env member
    simp [producedMessages, consumedMessages, disabled env member, zero]

private theorem auxiliary_memory_words
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (silent : ∀ component ∈ (HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++ resources,
      memoryChannel.toRaw ∉ component.circuit.channels) :
    HostLocalCore.auxiliaryMemory witness = (wordTables witness).flatMap (typedTableInteractionsWith · memoryChannel) := by
  have receivers : (HostLocalHandoff.receiverTables witness).flatMap (typedTableInteractionsWith · memoryChannel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply typedTableInteractions_nil
    apply silent
    apply List.mem_append_left
    rw [← HostLocalHandoff.receiverTables_components witness]
    exact List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  have resourcesSilent : ((HostLocalHandoff.resourceTables witness).drop 2).flatMap
      (typedTableInteractionsWith · memoryChannel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply typedTableInteractions_nil
    apply silent
    apply List.mem_append_right
    have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_drop, HostLocalHandoff.resourceTables_components] at component
    simpa only [HostHintReadHandoff.wordResources, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] using component
  have split : HostLocalHandoff.receiverTables witness ++ HostLocalHandoff.resourceTables witness =
      HostLocalCore.auxiliaryTables witness := List.take_append_drop _ _
  rw [HostLocalCore.auxiliaryMemory, ← split, List.flatMap_append, receivers, List.nil_append]
  rw [← List.take_append_drop 2 (HostLocalHandoff.resourceTables witness), List.flatMap_append,
    resourcesSilent, List.append_nil]
  rfl

variable {final : HostHintQueue.State (ZMod p)}

omit [Fact (2 ^ 25 < p)] in
private theorem messages_perm (left right : List (TypedInteraction (memoryChannel (p := p))))
    (perm : left.Perm right) :
    (producedMessages left).Perm (producedMessages right) ∧
      (consumedMessages left).Perm (consumedMessages right) :=
  ⟨(perm.filter _).map _, (perm.filter _).map _⟩

/-- Every active host Memory contribution of the installed source assembly belongs to its
word tables. The zero x12 pairs remain in the raw ledger and disappear only by signed activity. -/
theorem source_memory_messages
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))).Perm
      (producedMessages (LocalCore.memoryInterior (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) ++
        producedMessages ((wordTables (HostHintQueueBoundary.expanded witness)).flatMap (typedTableInteractionsWith · memoryChannel))) ∧
    (consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))).Perm
      (consumedMessages (LocalCore.memoryInterior (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) ++
        consumedMessages ((wordTables (HostHintQueueBoundary.expanded witness)).flatMap (typedTableInteractionsWith · memoryChannel))) := by
  have checked := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have interface := HostHintQueueBoundary.expanded_interface (source := source) (final := final)
    (source_interface (p := p) source.host.io.hints)
  have specs := queue_specs _ interface _ (HostHintQueueBoundary.source_authentication witness constraints) checked balance
  have empty := wrapper_messages_nil _ (wrapper_disabled _ interface checked balance specs)
  have words := auxiliary_memory_words (HostHintQueueBoundary.expanded witness) (source_memory_silent source final)
  have perm := HostLocalCore.memoryInterior_perm (HostHintQueueBoundary.expanded witness) checked
  have messages := messages_perm _ _ perm
  simpa only [producedMessages_append, consumedMessages_append, empty.1, empty.2, List.append_nil, words] using messages

/-- The actual CPU inventory with all installed hint-word Memory effects attached. -/
noncomputable def sourceExecutionRows
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)) : List (RowFacts p) :=
  (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map
    (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))))

private theorem source_data
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data = witness.data := rfl

/-- Every active physical Memory record is in its enlarged CPU row or an actual refresh pair.
No host access remains as an unaccounted side ledger. -/
theorem source_execution_memory_projection
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    TimedGrounding.pushesAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map Prod.snd) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))) : Multiset _) ∧
    TimedGrounding.pullsAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map Prod.fst) : Multiset _) =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))) : Multiset _) := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.expanded_constraints witness constraints)
  have original := LocalCore.executionRows_memory_projection _ checked loc
  rw [source_data] at original
  have enlarged := eventFacts_memory witness.data
    (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.expanded witness)))
    (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) loc
  have partition := source_words_partition witness constraints balanced _ (List.Perm.refl _)
  have groupedPushes := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr (partition.map (fun row => (touch row).2)))
  have groupedPulls := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr (partition.map (fun row => (touch row).1.1)))
  have words := word_memory_messages _ (wordTables_aligned (HostHintQueueBoundary.expanded witness))
  have messages := source_memory_messages witness constraints balanced
  have fullPushes := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr messages.1)
  have fullPulls := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr messages.2)
  rw [filter_coe_append, words.1] at fullPushes
  rw [filter_coe_append, words.2] at fullPulls
  constructor
  · rw [sourceExecutionRows, enlarged.1, groupedPushes, add_right_comm, original.1]
    exact fullPushes.symm
  · rw [sourceExecutionRows, enlarged.2, groupedPulls, add_right_comm, original.2]
    exact fullPulls.symm

/-- The full source/final inventories balance the enlarged execution rows and real refreshes.
This is record conservation before the grounding walk establishes predecessor value currency. -/
theorem source_execution_memory_balance
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
          (LocalCore.sourceWitness (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))) : Multiset _) +
      TimedGrounding.pushesAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map Prod.snd) : Multiset _) =
    Multiset.filter (fun message => MemoryMsg.locOf message = loc)
        (↑(FinalMemoryEnsemble.records (LocalCore.finalWitness
          (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))) : Multiset _) +
      TimedGrounding.pullsAt (sourceExecutionRows witness) loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑((LocalCore.memoryRefreshes (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))).map Prod.fst) : Multiset _) := by
  have physical := source_memory_records_perm witness constraints balanced
  have balance := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr physical)
  rw [filter_coe_append, filter_coe_append] at balance
  have projection := source_execution_memory_projection witness constraints balanced loc
  rw [add_assoc, add_assoc, projection.1, projection.2]
  exact balance

end SP1Clean.Soundness.HostHintReadCPU
