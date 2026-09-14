import SP1Clean.Soundness.HostHintReadLocalRecords

/-! # HINT_READ execution from authenticated installed records

Whole-witness record authentication may use the final persistent store. The current queue head
and the actual per-call cursor path restrict every requested node to the current allocation
frontier. The execution theorem therefore derives node/word bindings and local specifications;
current queue history, immutable allocation authentication, Memory representation guarantees,
and current register observations remain explicit inputs to mixed grounding.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintReadCoverage HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_records (env : Environment (ZMod p)) (row : Var HostHintReadChip.Inputs (ZMod p)) :
    eval env row.node = (eval env row).node ∧
      eval env row.endStep.word = (eval env row).endStep.word := by
  rcases row with ⟨call, previous, node, span, lastIndex, lastValue⟩
  cases node
  simp only [HostHintReadChip.Inputs.endStep, circuit_norm, and_self]

/-- The actual handler pulls both its node header and its terminal word record. -/
theorem handler_records (env : Environment (ZMod p)) :
    handler.operations.interactionValuesWith nodeChannel.toRaw env =
      [nodeChannel.pulledValue (input env).node] ∧
    handler.operations.interactionValuesWith wordChannel.toRaw env =
      [wordChannel.pulledValue (input env).endStep.word] := by
  constructor
  all_goals
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  · change (((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
      (size HostHintReadChip.Inputs)).interactionsWith nodeChannel.toRaw).map _ = _
    rw [HostHintReadChip.main_node_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, (eval_records _ _).1,
      eval_varFromOffset_valueFromOffset, input]
  · change (((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
      (size HostHintReadChip.Inputs)).interactionsWith wordChannel.toRaw).map _ = _
    rw [HostHintReadChip.main_word_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, (eval_records _ _).2,
      eval_varFromOffset_valueFromOffset, input]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_word (env : Environment (ZMod p)) (row : Var HintReadWordChip.Inputs (ZMod p))
    (last : Bool) : eval env (row.step last).word = ((eval env row).step last).word := by
  rcases row with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  cases ram
  cases last <;> simp only [HintReadWordChip.Inputs.step, circuit_norm]

private theorem consumer_record (row : HintReadCoverage.Row (p := p)) :
    (HintReadCoverage.view row.1).component.operations.interactionValuesWith wordChannel.toRaw row.2 =
      [wordChannel.pulledValue ((HintReadCoverage.rowInput row).step row.1).word] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HintReadWordChip.main row.1 (varFromOffset HintReadWordChip.Inputs 0)).operations
    (size HintReadWordChip.Inputs)).interactionValuesWith wordChannel.toRaw row.2 = _
  rw [HintReadWordChip.word_values, eval_word, eval_varFromOffset_valueFromOffset]
  rfl

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

private theorem handler_pull_mem (witness : EnsembleWitness (ensemble image source others resources channels))
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment)
    (channel : RawChannel (ZMod p)) (interaction : Interaction (ZMod p))
    (present : interaction ∈ handler.operations.interactionValuesWith channel env) :
    interaction ∈ witness.interactionsWith channel := by
  apply EnsembleWitness.mem_interactionsWith.mpr
  refine ⟨handlerTable witness, handlerTable_mem witness, ?_⟩
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp member
  apply List.mem_flatMap.mpr
  exact ⟨physical, physicalMem, (handlerTable_component witness) ▸ present⟩

private theorem consumer_pull_mem (witness : EnsembleWitness (ensemble image source others resources channels))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) :
    wordChannel.pulledValue ((HintReadCoverage.rowInput row).step row.1).word ∈
      witness.interactionsWith wordChannel.toRaw := by
  have present : wordChannel.pulledValue ((HintReadCoverage.rowInput row).step row.1).word ∈
      (wordTables witness).flatMap (·.interactionsWith wordChannel.toRaw) := by
    rw [TransitionView.readIndexedRows_interactions HintReadCoverage.variants
      (fun last => (HintReadCoverage.view last).component) _ _ (wordTables_aligned witness)]
    refine List.mem_flatMap.mpr ⟨row, member, ?_⟩
    change _ ∈ (HintReadCoverage.view row.1).component.operations.interactionValuesWith wordChannel.toRaw row.2
    rw [consumer_record]
    exact List.mem_cons_self ..
  obtain ⟨table, tableMem, present⟩ := List.mem_flatMap.mp present
  exact EnsembleWitness.mem_interactionsWith.mpr ⟨table, wordTables_mem witness table tableMem, present⟩

private theorem consumer_pointer (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment)
    (row : HintReadCoverage.Row (p := p))
    (rowMem : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness))
    (clock : HostHintReadPartition.clock (HintReadCoverage.rowInput row).previous =
      HostHintReadPartition.callClock env) :
    ((HintReadCoverage.rowInput row).step row.1).word.pointer = (input env).node.pointer := by
  have selected := balanced_for witness interface constraints balanced env member
  rw [handler_cursor] at selected
  have alignment := TransitionView.selectTables_aligned _ _
    (fun last => (HintReadCoverage.view last).component)
    (HostHintReadPartition.keepWord (HostHintReadPartition.callClock env)) (wordTables_aligned witness)
  have specs := wordSpecs.select (HostHintReadPartition.keepWord (HostHintReadPartition.callClock env))
  obtain ⟨path, perm, _, _, _, _, same⟩ := HintReadCoverage.ordered_cover _ _ _ alignment specs selected
  have included : row ∈ path := by
    apply perm.mem_iff.mpr
    rw [TransitionView.readIndexedRows_selectTables]
    exact List.mem_filter.mpr ⟨rowMem, by simpa only [HostHintReadPartition.keepWord,
      HostHintReadPartition.keepState, HintReadCoverage.rowInput, decide_eq_true_eq] using clock⟩
  exact congrArg (fun context => context.2.2) (same row included)

/-- Installed record balance authenticates the header and every consumed word at the call's
current frontier. The cursor enforces that all selected words refer to this same queue node. -/
theorem current_records (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) (handlerSpecs : (handlerTable witness).Spec)
    (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (store finalStore : Store) (extension : Extends store finalStore)
    (authenticated : RecordAuthentication witness finalStore)
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment)
    (hints : List Bytes) (current : (input env).previous.Binds store hints) :
    (input env).node.Binds store ∧ (input env).endStep.word.Binds store ∧
      ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness),
        HostHintReadPartition.clock (HintReadCoverage.rowInput row).previous = HostHintReadPartition.callClock env →
          ((HintReadCoverage.rowInput row).step row.1).word.Binds store := by
  have valid : handler.Spec env := by
    obtain ⟨physical, present, rfl⟩ := List.mem_map.mp member
    rw [← handlerTable_component witness]
    exact handlerSpecs physical present
  have bound : Address.toNat (input env).node.pointer ≤ store.size := by
    have head : (input env).previous.head = (input env).node.pointer := valid.2.2.2.2.2.2.1
    rw [← head]
    exact current.2.2.2.bound
  have node := (node_authenticated witness finalStore authenticated balanced (input env).node
    (handler_pull_mem witness env member _ _ (by rw [(handler_records env).1]; exact List.mem_cons_self ..))).2
  have ending := (word_authenticated witness finalStore authenticated balanced (input env).endStep.word
    (handler_pull_mem witness env member _ _ (by rw [(handler_records env).2]; exact List.mem_cons_self ..))).2
  refine ⟨node.restrict extension bound, ending.restrict extension bound, ?_⟩
  intro row rowMem clock
  apply ((word_authenticated witness finalStore authenticated balanced _ (consumer_pull_mem witness row rowMem)).2).restrict extension
  rw [consumer_pointer witness interface constraints balanced wordSpecs env member row rowMem clock]
  exact bound

/-- Actual AIR constraints and balance give successful HINT_READ dispatch and the complete padded
write inventory. Source authentication and current queue/register grounding remain explicit;
no local specifications or per-record binding premises are supplied by the caller. -/
theorem run_of_authenticated_witness (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources)
    (pulls : ∀ component ∈ others.map (·.component) ++ resources, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (finalStore : Store) (authenticated : RecordAuthentication witness finalStore)
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment)
    (host : HostState) (store : Store) (extension : Extends store finalStore)
    (current : (input env).previous.Binds store host.io.hints)
    (running : host.exitCode = none) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 (input env).call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 (input env).call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 (input env).call.arg2)) :
    ∃ bytes rest, host.io.hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      host.run ⟨{ readOnly := image.readOnly }, p⟩ context = some (HostHintReadChip.execution (input env) host bytes rest) ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) (wordTables witness))).map
        HintReadWrites.produced).Perm (wordWrites (Address.toNat (input env).span.start) bytes) := by
  have handlerSpecs := handler_spec witness interface finalStore authenticated constraints balanced
  have wordSpecs := word_steps witness interface finalStore authenticated constraints balanced
  obtain ⟨header, ending, words⟩ := current_records witness interface constraints balanced handlerSpecs wordSpecs
    store finalStore extension authenticated env member host.io.hints current
  exact run_of_witness witness interface pulls constraints balanced handlerSpecs wordSpecs env member
    host store current header ending words running context code arg1 arg2

end SP1Clean.Soundness.HostHintReadLocal
