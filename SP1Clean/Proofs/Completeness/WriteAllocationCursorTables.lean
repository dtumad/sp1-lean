import SP1Clean.Proofs.Completeness.WriteAllocationBatch
import SP1Clean.Proofs.Completeness.WriteAllocationWordTables
import ToClean.Air.GuardedLedger

/-! # Physical cursor ledgers of the four WRITE allocation tables

The following equalities retain the original occurrence order, activity and terminal gates,
including every disabled row in the once-padded demand tables.
-/

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat WriteEffects
open scoped Classical

private abbrev F := ZMod SP1Prime

private theorem eval_first (env : Environment F) (r : Var Open F) :
    Eval.eval env r.first = (ProvableStruct.eval env r).first := by
  rcases r with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _⟩
  simp only [Open.first, Open.source, Open.count, Open.outgoing, scale, ClockParts.high24, ClockParts.low24, circuit_norm]

private theorem eval_last (env : Environment F) (r : Var Open F) :
    Eval.eval env r.last = (ProvableStruct.eval env r).last := by
  rcases r with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _⟩
  simp only [Open.last, Open.source, Open.outgoing, scale, ClockParts.high24, ClockParts.low24, circuit_norm]

/-- Cursor occurrences of a guarded allocation open input, in their physical order. -/
def openCursors (r : Open F × F) : List (Interaction F) :=
  [cursorChannel.pushedIfValue r.2 r.1.first, cursorChannel.pulledIfValue r.2 r.1.last]

private theorem open_values (r : Var Open F) (n : Nat) (env : Environment F) :
    ((openMain r).operations n).interactionValuesWith cursorChannel.toRaw env =
      [cursorChannel.pushedValue (ProvableStruct.eval env r).first, cursorChannel.pulledValue (ProvableStruct.eval env r).last] := by
  have raw : ((openMain r).operations n).interactionsWith cursorChannel.toRaw =
      [(cursorChannel.pushed r.first).toRaw, (cursorChannel.pulled r.last).toRaw] := by
    rw [open_ledger]
    simp [cursorChannel, queueEffectChannel, HostHintQueue.stateChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    eval_first, eval_last]

/-- Exact guarded cursor occurrences in an arbitrary physical call header environment. -/
theorem openInput_cursors (env : Environment F) :
    (openComponent (p := SP1Prime)).operations.interactionValuesWith cursorChannel.toRaw env =
      openCursors (openComponent.rowInput env) := by
  let I := ProvablePair Open field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main openCircuit openSupported input).operations (size I)).interactionValuesWith _ env =
    openCursors (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((openMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [open_values]
  have proj (i : Var (ProvablePair Open field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons, List.map_nil, Channel.pushedValue, Channel.pulledValue, Channel.pushedIfValue,
    Channel.pulledIfValue, mul_one, Guarded.eval_activity, proj, input, eval_varFromOffset_valueFromOffset, openCursors]

/-- The actual guarded allocation open component filled at Clean's demand height. -/
def openTable (rows : List (Open F)) (data : ProverData F)
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table F :=
  Table.ofInputs openComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- Every physically allocated open row has a checked witness. -/
theorem openTable_valid (rows : List (Open F)) (valid : ∀ r ∈ rows, r.Valid) (data : ProverData F) (fit) :
    (openTable rows data fit).Constraints ∧ (openTable rows data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all Open.Valid valid

/-- Complete signed cursor ledger of the generated open table, including padding. -/
theorem openTable_cursors (rows : List (Open F)) (data : ProverData F) (fit) :
    (openTable rows data fit).interactionsWith cursorChannel.toRaw =
      (WitnessGeneration.guardedRows rows).flatMap openCursors :=
  Table.ofInputs_ledger openComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
    cursorChannel.toRaw openCursors openInput_cursors

private theorem eval_before (env : Environment F) (r : Var Step F) :
    Eval.eval env r.before = (ProvableStruct.eval env r).before := by
  rcases r with ⟨⟨⟨_, _, _, _⟩, ⟨_, _, _⟩⟩, _, _, _, _, _⟩
  simp only [Step.before, Step.source, Step.length, threeLimbs, scale, circuit_norm]

private theorem eval_after (env : Environment F) (r : Var Step F) :
    Eval.eval env r.after = (ProvableStruct.eval env r).after := by
  rcases r with ⟨⟨⟨_, _, _, _⟩, ⟨_, _, _⟩⟩, _, _, _, _, _⟩
  simp only [Step.after, Step.source, Step.length, threeLimbs, scale, HintNodeAllocate.Inputs.next, circuit_norm]

/-- Cursor occurrences of a guarded allocation step input, in their physical order. -/
def stepCursors (r : Step F × F) : List (Interaction F) :=
  [cursorChannel.pulledIfValue r.2 r.1.before, cursorChannel.pushedIfValue r.2 r.1.after]

private theorem step_values (r : Var Step F) (n : Nat) (env : Environment F) :
    ((stepMain r).operations n).interactionValuesWith cursorChannel.toRaw env =
      [cursorChannel.pulledValue (ProvableStruct.eval env r).before, cursorChannel.pushedValue (ProvableStruct.eval env r).after] := by
  have raw : ((stepMain r).operations n).interactionsWith cursorChannel.toRaw =
      [(cursorChannel.pulled r.before).toRaw, (cursorChannel.pushed r.after).toRaw] := by
    rw [step_ledger _ _ _ (by simp [cursorChannel, Channels.byteChannel, circuit_norm])]
    simp [cursorChannel, recordChannel, HostHintQueue.nodeChannel, contentsChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    eval_before, eval_after]

/-- Exact guarded cursor occurrences in an arbitrary physical fresh node environment. -/
theorem stepInput_cursors (env : Environment F) :
    (stepComponent (p := SP1Prime)).operations.interactionValuesWith cursorChannel.toRaw env =
      stepCursors (stepComponent.rowInput env) := by
  let I := ProvablePair Step field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main stepCircuit stepSupported input).operations (size I)).interactionValuesWith _ env =
    stepCursors (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((stepMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [step_values]
  have proj (i : Var (ProvablePair Step field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons, List.map_nil, Channel.pushedValue, Channel.pulledValue, Channel.pushedIfValue,
    Channel.pulledIfValue, mul_one, Guarded.eval_activity, proj, input, eval_varFromOffset_valueFromOffset, stepCursors]

/-- The actual guarded allocation step component filled at Clean's demand height. -/
def stepTable (rows : List (Step F)) (data : ProverData F)
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table F :=
  Table.ofInputs stepComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- Every physically allocated step row has a checked witness. -/
theorem stepTable_valid (rows : List (Step F)) (valid : ∀ r ∈ rows, r.Valid) (data : ProverData F) (fit) :
    (stepTable rows data fit).Constraints ∧ (stepTable rows data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all Step.Valid valid

/-- Complete signed cursor ledger of the generated step table, including padding. -/
theorem stepTable_cursors (rows : List (Step F)) (data : ProverData F) (fit) :
    (stepTable rows data fit).interactionsWith cursorChannel.toRaw =
      (WitnessGeneration.guardedRows rows).flatMap stepCursors :=
  Table.ofInputs_ledger stepComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
    cursorChannel.toRaw stepCursors stepInput_cursors

namespace Words

private theorem eval_start (env : Environment F) (r : Var Contents F) :
    Eval.eval env (start r) = start (ProvableStruct.eval env r) := by
  rcases r with ⟨_, _, _, _, _⟩
  simp only [start, circuit_norm]
  change eval env (#v[0,0,0] : fields 3 (Expression F)) = #v[0,0,0]
  simp only [circuit_norm]

/-- Cursor occurrences of a guarded allocation seed input, in their physical order. -/
def seedCursors (r : Contents F × F) : List (Interaction F) :=
  [cursorChannel.pushedIfValue r.2 (start r.1)]

private theorem seed_values (r : Var Contents F) (n : Nat) (env : Environment F) :
    ((seedMain r).operations n).interactionValuesWith cursorChannel.toRaw env =
      [cursorChannel.pushedValue (start (ProvableStruct.eval env r))] := by
  have raw : ((seedMain r).operations n).interactionsWith cursorChannel.toRaw =
      [(cursorChannel.pushed (start r)).toRaw] := by
    rw [Operations.interactionsWith, seed_ledger]
    simp [contentsChannel, cursorChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed,
    eval_start]

/-- Exact guarded cursor occurrences in an arbitrary physical contents header environment. -/
theorem seedInput_cursors (env : Environment F) :
    (seedComponent (p := SP1Prime)).operations.interactionValuesWith cursorChannel.toRaw env =
      seedCursors (seedComponent.rowInput env) := by
  let I := ProvablePair Contents field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main seedCircuit seedSupported input).operations (size I)).interactionValuesWith _ env =
    seedCursors (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((seedMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [seed_values]
  have proj (i : Var (ProvablePair Contents field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons, List.map_nil, Channel.pushedValue, Channel.pushedIfValue,
    mul_one, Guarded.eval_activity, proj, input, eval_varFromOffset_valueFromOffset, seedCursors]

/-- Complete signed cursor ledger of the generated seed table, including padding. -/
theorem seedTable_cursors (rows : List (Contents F)) (data : ProverData F) (fit) :
    (seedTable rows data fit).interactionsWith cursorChannel.toRaw =
      (WitnessGeneration.guardedRows rows).flatMap seedCursors :=
  Table.ofInputs_ledger seedComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
    cursorChannel.toRaw seedCursors seedInput_cursors

private theorem eval_prior (env : Environment F) (r : Var Row F) :
    Eval.eval env r.prior = (ProvableStruct.eval env r).prior := by
  rcases r with ⟨⟨_, _, _⟩, _, _, _, ⟨_, _⟩, _, _⟩
  simp only [circuit_norm]

private theorem eval_next (env : Environment F) (r : Var Row F) :
    Eval.eval env r.next = (ProvableStruct.eval env r).next := by
  rcases r with ⟨⟨_, _, _⟩, _, _, _, ⟨_, _⟩, _, _⟩
  simp only [Row.next, circuit_norm]

private theorem eval_more (env : Environment F) (r : Var Row F) :
    Eval.eval env r.payload.more = (ProvableStruct.eval env r).payload.more := by
  rcases r with ⟨⟨_, _, _⟩, _, _, _, ⟨_, _⟩, _, _⟩
  simp only [Payload.more, circuit_norm]

/-- Cursor occurrences of a guarded allocation word input, in their physical order. -/
def wordCursors (r : Row F × F) : List (Interaction F) :=
  [cursorChannel.pulledIfValue r.2 r.1.prior, cursorChannel.pushedIfValue (r.2 * r.1.payload.more) r.1.next]

private theorem word_values (r : Var Row F) (n : Nat) (env : Environment F) :
    ((wordMain r).operations n).interactionValuesWith cursorChannel.toRaw env =
      [cursorChannel.pulledValue (ProvableStruct.eval env r).prior, cursorChannel.pushedIfValue (ProvableStruct.eval env r).payload.more (ProvableStruct.eval env r).next] := by
  have raw : ((wordMain r).operations n).interactionsWith cursorChannel.toRaw =
      [(cursorChannel.pulled r.prior).toRaw, (cursorChannel.pushedIf r.payload.more r.next).toRaw] := by
    rw [Operations.interactionsWith, word_ledger]
    simp [cursorChannel, blockChannel, HostHintQueue.wordChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled,
    Channel.eval_pushedIf, eval_prior, eval_next, eval_more]

/-- Exact guarded cursor occurrences in an arbitrary physical contents word environment. -/
theorem wordInput_cursors (env : Environment F) :
    (wordComponent (p := SP1Prime)).operations.interactionValuesWith cursorChannel.toRaw env =
      wordCursors (wordComponent.rowInput env) := by
  let I := ProvablePair Row field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main wordCircuit wordSupported input).operations (size I)).interactionValuesWith _ env =
    wordCursors (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [word_values]
  have proj (i : Var (ProvablePair Row field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons, List.map_nil, Channel.pulledValue, Channel.pushedIfValue,
    Channel.pulledIfValue, mul_one, Guarded.eval_activity, proj, input, eval_varFromOffset_valueFromOffset, wordCursors]

/-- Complete signed cursor ledger of the generated word table, including padding. -/
theorem wordTable_cursors (rows : List (Row F)) (data : ProverData F) (fit) :
    (wordTable rows data fit).interactionsWith cursorChannel.toRaw =
      (WitnessGeneration.guardedRows rows).flatMap wordCursors :=
  Table.ofInputs_ledger wordComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
    cursorChannel.toRaw wordCursors wordInput_cursors

end Words
end SP1Clean.WriteAllocation
