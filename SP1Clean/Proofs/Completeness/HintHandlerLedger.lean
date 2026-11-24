import SP1Clean.Proofs.Completeness.HintHandlerTables

/-! # Complete physical immutable demand of the three HINT headers and two word tables

Each equation below starts with the original Clean row interactions. In particular an
inactive HINT_READ row retains two independent zero-weight immutable record sites, while
the empty length circuit has no such site. Padded transfer rows are retained separately.
-/

namespace SP1Clean.TraceGen.HintHandlers
open Circuit Air.Flat Semantics HintQueue Machine FormalModel.Shard Soundness HostHintQueue WitnessGeneration
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)

private theorem read_sites {M : TypeMap} [ProvableType M] (ch : Channel F M) (record : HostHintReadChip.Inputs F → M F)
    (point : ∀ env, HostHintReadCoverage.handler.operations.interactionValuesWith ch.toRaw env =
      [ch.pulledIfValue (env HostHintReadCoverage.activity) (record (HostHintReadCoverage.input env))]) :
    (readTable run data).interactionsWith ch.toRaw =
      (guardedRows (F := F) (readRows (history image source events))).map (fun r => ch.pulledIfValue r.2 (record r.1)) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger
  case bound =>
    exact (guardedRows_length _).trans_le (((tables_heights run data).1.symm.le.trans (tables_heights run data).2.1).trans (by decide))
  case demand => intro _; trivial
  intro env
  have sites := point env
  rw [HostHintReadCoverage.decoded_activity] at sites
  exact sites

/-- The original HINT_READ table requests both records on every physical row with its actual weight. -/
theorem readTable_records :
    let rs := guardedRows (F := F) (readRows (history image source events))
    (readTable run data).interactionsWith nodeChannel.toRaw = rs.map (fun r => nodeChannel.pulledIfValue r.2 r.1.node) ∧
    (readTable run data).interactionsWith wordChannel.toRaw = rs.map (fun r => wordChannel.pulledIfValue r.2 r.1.endStep.word) :=
  ⟨read_sites run data nodeChannel _ (fun env => (HostHintReadLocal.handler_record_sites env).1),
   read_sites run data wordChannel (fun r => r.endStep.word) (fun env => (HostHintReadLocal.handler_record_sites env).2)⟩

/-- Nonempty HINT_LEN requests its head on every physical row with the stored activity. -/
theorem lengthTable_nodes :
    (lengthTable run false data).interactionsWith nodeChannel.toRaw =
      (guardedRows (F := F) (lengthRows false (history image source events))).map (fun r => nodeChannel.pulledIfValue r.2 r.1.node) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger
  case bound =>
    have height := (tables_heights run data).2.2.1 false
    exact (guardedRows_length _).trans_le ((height.1.symm.le.trans height.2).trans (by decide))
  case demand => intro _; trivial
  intro env
  have read (r : Var HostHintLengthChip.Inputs F) : eval env r.node = (eval env r).node := by
    rcases r with ⟨a, b, c⟩
    cases c
    simp only [circuit_norm]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change (((HostHintLengthChip.guardedCircuit false).main (varFromOffset HostHintLengthChip.RowInput 0)).operations
    (size HostHintLengthChip.RowInput)).interactionValuesWith nodeChannel.toRaw env = _
  rw [HostHintLengthChip.guarded_node_values, Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
  simp only [Bool.false_eq_true, ite_false, read]
  have decoded := eval_varFromOffset_valueFromOffset HostHintLengthChip.RowInput 0 env
  rw [CircuitType.eval_var_provablePair] at decoded
  exact congrArg (fun x : HostHintLengthChip.Inputs F =>
    [nodeChannel.pulledIfValue (valueFromOffset HostHintLengthChip.RowInput 0 env).2 x.node]) (congrArg Prod.fst decoded)

private theorem silent (table : Table F) (ch : RawChannel F)
    (outside : ch.name ∉ table.component.circuit.channels.map RawChannel.name) : table.interactionsWith ch = [] :=
  table.interactionsWith_nil_of_channel_not_mem fun used => outside (List.mem_map_of_mem used)

/-- All immutable node sites of the two transfer tables and the empty length table are absent,
and neither length variant has an immutable word site. -/
theorem silent_records :
    (lengthTable run true data).interactionsWith nodeChannel.toRaw = [] ∧
    (∀ empty, (lengthTable run empty data).interactionsWith wordChannel.toRaw = []) ∧
    (∀ last, (transferTable run last data).interactionsWith nodeChannel.toRaw = []) := by
  refine ⟨?_, ?_, ?_⟩
  · apply silent
    exact of_decide_eq_true rfl
  · intro empty
    apply silent
    cases empty <;> exact of_decide_eq_true rfl
  · intro last
    apply silent
    cases last <;> exact of_decide_eq_true rfl

/-- Each original transfer table requests its independent immutable word on every physical row. -/
theorem transferTable_words (last : Bool) :
    (transferTable run last data).interactionsWith wordChannel.toRaw =
      (HintReadTransfers.physicalInputs last (HintReadTransfers.history image source events)).map
        (fun r => wordChannel.pulledIfValue r.2 ((r.1.step last).word)) := by
  rw [List.map_eq_flatMap]
  apply HintReadTransfers.wordTable_ledger
  intro env
  have sites := HostHintReadLocal.consumer_record (p := SP1Prime) (last, env)
  have activity : HintReadCoverage.rowActivity (last, env) = (valueFromOffset HintReadWordChip.RowInput 0 env).2 := by
    rw [← eval_varFromOffset_valueFromOffset HintReadWordChip.RowInput 0 env, ← Guarded.eval_activity]
    simp only [HintReadCoverage.rowActivity, varFromOffset_pair, Nat.zero_add]
  rw [activity] at sites
  exact sites

private theorem header_messages (rows : List Row) :
    ((readRows rows).map HostHintReadChip.Inputs.node ++ (lengthRows false rows).map HostHintLengthChip.Inputs.node).Perm
      (rows.flatMap Row.nodes) ∧
    (readRows rows).map (fun r => r.endStep.word) = rows.flatMap Row.words := by
  induction rows with
  | nil => exact ⟨.nil, rfl⟩
  | cons first rest ih =>
    cases first with
    | read r =>
      simpa [readRows, lengthRows, Row.nodes, Row.words] using And.intro (ih.1.cons r.node) (congrArg (List.cons r.endStep.word) ih.2)
    | length empty r =>
      cases empty
      · simpa [readRows, lengthRows, Row.nodes, Row.words] using And.intro (List.perm_middle.trans (ih.1.cons r.node)) ih.2
      · simpa [readRows, lengthRows, Row.nodes, Row.words] using ih

private theorem transfer_messages (rows : List (Bool × HintReadWordChip.RowInput F)) :
    ((HintReadTransfers.selected false rows).map (fun r => (r.1.step false).word) ++
      (HintReadTransfers.selected true rows).map (fun r => (r.1.step true).word)).Perm (rows.map transferWord) := by
  induction rows with
  | nil => exact .nil
  | cons first rest ih =>
    rcases first with ⟨last, r⟩
    cases last
    · simpa [HintReadTransfers.selected, transferWord] using ih.cons ((r.1.step false).word)
    · simpa [HintReadTransfers.selected, transferWord] using List.perm_middle.trans (ih.cons ((r.1.step true).word))

include run in
private theorem guarded_transfers (last : Bool) :
    let ws := HintReadTransfers.history image source events
    HintReadTransfers.physicalInputs last ws = guardedRows ((HintReadTransfers.selected last ws).map Prod.fst) := by
  let selected := HintReadTransfers.selected last (HintReadTransfers.history image source events)
  have active (row : HintReadWordChip.RowInput F) (h : row ∈ selected) : row.2 = 1 := by
    obtain ⟨e, seen, rfl⟩ := List.mem_map.mp h
    exact HintReadTransfers.history_active run e (List.mem_filter.mp seen).1
  have rebuild : (selected.map Prod.fst).map (fun r => (r, (1 : F))) = selected := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id selected]
    apply List.map_congr_left
    intro row h
    exact Prod.ext rfl (active row h).symm
  dsimp only
  change selected ++ _ = guardedRows (selected.map Prod.fst)
  simp only [guardedRows, List.length_map, rebuild]
  rfl

private theorem transfer_sum (last : Bool) (msg : Array F) :
    balanceOf ((transferTable run last data).interactionsWith wordChannel.toRaw) msg =
      balanceOf (((HintReadTransfers.selected last (HintReadTransfers.history image source events)).map
        (fun r => (r.1.step last).word)).map wordChannel.pulledValue) msg := by
  rw [transferTable_words, guarded_transfers run last,
    guarded_pull_sum wordChannel _ (fun r : HintReadWordChip.Inputs F => (r.step last).word)]
  simp only [List.map_map, Function.comp_def]

/-- Physical slots 63, 82, 83, 84, 85 in their original order. -/
noncomputable def readerTables : List (Table F) :=
  [readTable run data, lengthTable run false data, lengthTable run true data, transferTable run false data, transferTable run true data]

/-- The signed physical requests equal all typed execution reads with multiplicity. Every
zero-weight physical occurrence remains in the five physical ledgers on the left. -/
theorem reader_sums (msg : Array F) :
    let q := HintQueueReaders.history image source events
    balanceOf ((readerTables run data).flatMap (·.interactionsWith nodeChannel.toRaw)) msg =
      balanceOf ((q.flatMap HintQueueReaders.Demand.nodes).map nodeChannel.pulledValue) msg ∧
    balanceOf ((readerTables run data).flatMap (·.interactionsWith wordChannel.toRaw)) msg =
      balanceOf ((q.flatMap HintQueueReaders.Demand.words).map wordChannel.pulledValue) msg := by
  obtain ⟨rNode, rWord⟩ := readTable_records run data
  obtain ⟨empty, lengths, transfers⟩ := silent_records run data
  obtain ⟨ns, ws⟩ := history_reads run
  obtain ⟨parts, heads⟩ := header_messages (history image source events)
  simp only [readerTables, List.flatMap_cons, List.flatMap_nil, List.append_nil, empty, lengths, transfers,
    List.nil_append, balanceOf_append]
  constructor
  · rw [rNode, lengthTable_nodes, guarded_pull_sum nodeChannel _ HostHintReadChip.Inputs.node,
      guarded_pull_sum nodeChannel _ HostHintLengthChip.Inputs.node, ← balanceOf_append, ← List.map_append, ← ns]
    exact balanceOf_perm (parts.map nodeChannel.pulledValue)
  · rw [rWord, guarded_pull_sum wordChannel _ (fun r : HostHintReadChip.Inputs F => r.endStep.word),
      transfer_sum, transfer_sum, ← balanceOf_append, ← List.map_append, ← balanceOf_append, ← List.map_append, heads]
    exact balanceOf_perm (((transfer_messages _).append_left _ |>.trans ws).map wordChannel.pulledValue)

end SP1Clean.TraceGen.HintHandlers
