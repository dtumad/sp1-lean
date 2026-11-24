import SP1Clean.Proofs.Completeness.HintSnapshotTables
import SP1Clean.Proofs.Operations.HintQueueSnapshot
import ToClean.Air.MessageFilter
import ToClean.Air.TableEvaluation

/-! # Closing the generated outgoing queue walk

The seal supplies the first cursor. Within each buffer the cursor retains both node
identities. The padded last word moves to the tail, and the final word reaches zero.
-/

namespace SP1Clean.HostHintSnapshot
open Circuit Air.Flat Semantics Semantics.HintQueue HostHintQueue
variable {p : ℕ} [Fact p.Prime]

/-- Both signed cursor occurrences of one physical word row, including inactive padding. -/
def walkValues (r : Inputs (ZMod p)) : List (Interaction (ZMod p)) :=
  [channel.pulledIfValue r.2.2 (r.1.before r.2.1), channel.pushedIfValue r.1.active (r.1.after r.2.1)]

private theorem walk_values (hints : List Bytes) (r : Var Inputs (ZMod p)) (env : Environment (ZMod p)) (offset : ℕ) :
    ((main hints r).operations offset).interactionValuesWith channel.toRaw env = walkValues (eval env r) := by
  have occurrences : ((main hints r).operations offset).interactionsWith channel.toRaw =
      [(channel.pulledIf r.2.2 (r.1.before r.2.1)).toRaw, (channel.pushedIf r.1.active (r.1.after r.2.1)).toRaw] := by
    rw [Operations.interactionsWith, ledger]
    simp [channel, nodeChannel, wordChannel, Channel.toRaw, circuit_norm]
  rw [Operations.interactionValuesWith, occurrences]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, Channel.eval_pushedIf, walkValues]
  rcases r with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _⟩, _⟩
  simp only [Shape.before, Shape.after, circuit_norm]
  simp only [ProvableType.eval_fields, Vector.map_map, Function.comp_def]

/-- The complete generated cursor ledger uses the physical rows at their canonical data. -/
theorem tableFor_walk (store : Store) (head : ℕ) (hints : List Bytes) (fit : fits hints = true)
    (data : ProverData (ZMod p)) :
    (tableFor store head hints fit data).interactionsWith channel.toRaw =
      (inputsFor (p := p) store head hints).flatMap walkValues := by
  dsimp only [tableFor]
  erw [Table.build_interactions]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r _
  let c := component (p := p) hints
  let rows := inputsFor (p := p) store head hints
  let own := c.inputData rows data
  let env := Environment.fromArray (c.buildRow r own (.empty _)) own
  change c.operations.interactionValuesWith channel.toRaw env = _
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((main hints (varFromOffset Inputs 0)).operations (size Inputs)).interactionValuesWith channel.toRaw env = _
  rw [walk_values, eval_varFromOffset_valueFromOffset]
  exact congrArg walkValues (c.rowInput_buildRow r own own (.empty _))

private def position (start head tail words i : ℕ) : Cursor (ZMod p) :=
  ⟨Address.ofNat (start + i), Address.ofNat (if i = words then tail else head),
    if 0 < i ∧ i < words then Address.ofNat tail else 0⟩

private theorem step_positions (start head tail length i : ℕ) (word : BitVec 64) (live : i < length / 8 + 1) :
    let s := shape (p := p) (start + i) i length word
    let l : Links (ZMod p) := ⟨Address.ofNat head, Address.ofNat tail⟩
    s.before l = position start head tail (length / 8 + 1) i ∧
      s.after l = position start head tail (length / 8 + 1) (i + 1) := by
  have before : i ≠ length / 8 + 1 := by omega
  have nextPositive : 0 < i + 1 := by omega
  have begins : 0 < i ↔ i ≠ 0 := by omega
  have ends : i + 1 = length / 8 + 1 ↔ i = length / 8 := by omega
  have continues : i + 1 < length / 8 + 1 ↔ i ≠ length / 8 := by omega
  have erased : (Address.ofNat (p := p) tail).map (fun _ => (0 : ZMod p)) = 0 := by
    ext j hj
    simp
  simp only [Shape.before, Shape.after, position, shape, before, live, nextPositive, begins, ends,
    continues, and_true, true_and, ↓reduceIte]
  by_cases first : i = 0 <;> by_cases last : i = length / 8
  all_goals
    first | have hf : (i = 0) = True := eq_true first | have hf : (i = 0) = False := eq_false first
    first | have hl : (i = length / 8) = True := eq_true last | have hl : (i = length / 8) = False := eq_false last
    simp [ne_eq, hf, hl, erased, Nat.add_assoc]


private def indicator (cursor : Cursor (ZMod p)) (msg : Array (ZMod p)) : ZMod p :=
  if (toElements cursor).toArray = msg then 1 else 0

private theorem active_delta (s : Shape (ZMod p)) (links : Links (ZMod p)) (active : s.active = 1)
    (msg : Array (ZMod p)) : balanceOf (walkValues (s, links, 1)) msg =
      indicator (s.after links) msg - indicator (s.before links) msg := by
  by_cases before : (toElements (s.before links)).toArray = msg <;>
    by_cases after : (toElements (s.after links)).toArray = msg <;>
    simp [walkValues, balanceOf, Channel.pulledIfValue, Channel.pushedIfValue, Interaction.signedMult,
      active, indicator, before, after]

private theorem buffer_balance (start head tail : ℕ) (bytes : Bytes) (msg : Array (ZMod p)) :
    let links : Links (ZMod p) := ⟨Address.ofNat head, Address.ofNat tail⟩
    balanceOf (((bufferShapes start bytes).map fun s => (s, links, 1)).flatMap walkValues) msg =
      indicator (endpoint (start + wordCount bytes) (Address.ofNat tail)) msg -
      indicator (endpoint start (Address.ofNat head)) msg := by
  let links : Links (ZMod p) := ⟨Address.ofNat head, Address.ofNat tail⟩
  let row (i : ℕ) : Shape (ZMod p) := shape (start + i) i bytes.length (arrayWord bytes.toArray i)
  let atWord (i : ℕ) := position (p := p) start head tail (wordCount bytes) i
  have prefixSum (n : ℕ) (bound : n ≤ wordCount bytes) :
      balanceOf ((List.range n).flatMap (fun i => walkValues (row i, links, 1))) msg =
        indicator (atWord n) msg - indicator (atWord 0) msg := by
    induction n with
    | zero => simp [balanceOf]
    | succ n ih =>
      have steps := step_positions (p := p) start head tail bytes.length n (arrayWord bytes.toArray n) bound
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, balanceOf_append, ih (by omega),
        active_delta _ _ rfl, show (row n).before links = atWord n from steps.1,
        show (row n).after links = atWord (n + 1) from steps.2]
      abel
  have zero : atWord 0 = endpoint start (Address.ofNat head) := by
    simp [atWord, position, endpoint, wordCount]
  have last : atWord (wordCount bytes) = endpoint (start + wordCount bytes) (Address.ofNat tail) := by
    simp [atWord, position, endpoint]
  have exactSum := prefixSum (wordCount bytes) (by rfl)
  rw [zero, last] at exactSum
  simpa only [bufferShapes, List.flatMap_map, List.size_toArray, Function.comp_apply, links, row, wordCount]
    using exactSum

private theorem address_zero : Address.ofNat (p := p) 0 = 0 := by
  ext i inside
  interval_cases i <;> simp [Address.ofNat]

private theorem live_balance [Fact (2 ^ 17 < p)] {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) (start : ℕ) (msg : Array (ZMod p)) :
    balanceOf ((liveInputs (p := p) store start head hints).flatMap walkValues) msg =
      indicator (endpoint (start + wordRows hints) 0) msg - indicator (endpoint start (Address.ofNat head)) msg := by
  induction hints generalizing start head tails with
  | nil =>
    cases tails with
    | nil =>
      have ended : head = 0 := read
      simp [liveInputs, wordRows, ended, address_zero, balanceOf]
    | cons => contradiction
  | cons bytes rest ih =>
    cases tails with
    | nil => contradiction
    | cons tail tails =>
      obtain ⟨bounded, down, indices, node, suffix⟩ := read
      have found := (readsNode_iff bounded down indices).mp node
      simp only [liveInputs, found, Option.map_some, Option.getD_some, List.flatMap_append, balanceOf_append,
        buffer_balance, ih suffix, wordRows, List.map_cons, List.sum_cons, Nat.add_assoc]
      abel

private theorem padding_balance (n : ℕ) (msg : Array (ZMod p)) :
    balanceOf ((List.replicate n ((Shape.padding, 0, 0) : Inputs (ZMod p))).flatMap walkValues) msg = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, balanceOf_append, ih, add_zero]
    simp only [walkValues, balanceOf_cons, Shape.padding, Channel.pulledIfValue, Channel.pushedIfValue,
      Interaction.signedMult, neg_zero, ite_self, zero_add]
    rfl

/-- The active fixed word walk cancels at every middle cursor. Its complete padded ledger
is the difference between the public terminal word ordinal and the actual incoming head. -/
theorem tableFor_walk_balance [Fact (2 ^ 17 < p)] {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) (fit : fits hints = true) (data : ProverData (ZMod p))
    (msg : Array (ZMod p)) :
    balanceOf ((tableFor store head hints fit data).interactionsWith channel.toRaw) msg =
      (if (toElements (endpoint (p := p) (wordRows hints) 0)).toArray = msg then 1 else 0) -
      (if (toElements (endpoint (p := p) 0 (Address.ofNat head))).toArray = msg then 1 else 0) := by
  rw [tableFor_walk, inputs_eq_padded store head hints fit, List.flatMap_append, balanceOf_append, padding_balance,
    add_zero, live_balance read, Nat.zero_add]
  rfl

namespace Seal

/-- The generated seal consumes the complete private state exactly once, supplies the live
walk, receives its public end, and publishes the next shard's canonical state. -/
theorem tableFor_ledger (hints : List Bytes) (state : State (ZMod p)) (data : ProverData (ZMod p)) :
    (tableFor hints state data).interactions =
      [stateChannel.pulledValue state, channel.pushedValue (endpoint 0 state.head),
       channel.pulledValue (endpoint (wordRows hints) 0), stateChannel.pushedValue (HostHintQueueBoundary.initial hints)] := by
  dsimp only [tableFor]
  erw [Table.build_interactionValues]
  let c := component (p := p) hints
  let input : c.Input (ZMod p) := (1, state, 1)
  let own := c.inputData [input] data
  let env := Environment.fromArray (c.buildRow input own (.empty _)) own
  let r := varFromOffset Inputs (F := ZMod p) 0
  change ([input].flatMap fun row => c.operations.interactionValues
    (Environment.fromArray (c.buildRow row own (.empty _)) own)) = _
  rw [List.flatMap_singleton]
  change c.operations.interactionValues env = _
  rw [Operations.interactionValues, Component.interactions_eq]
  change (((main hints r).operations (size Inputs)).interactions).map (·.eval env) = _
  rw [ledger]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled,
    Channel.eval_pushedIf, ProvableType.eval_const]
  have cells : eval env r = ((1, state, 1) : Inputs (ZMod p)) :=
    (eval_varFromOffset_valueFromOffset ..).trans (c.rowInput_buildRow _ own own _)
  have head : eval env r.2.1.head = state.head := by
    simpa only [circuit_norm] using congrArg (fun x : Inputs (ZMod p) => x.2.1.head) cells
  have cursor : ProvableStruct.eval env r.2.1 = state := by
    simpa only [circuit_norm] using congrArg (fun x : Inputs (ZMod p) => x.2.1) cells
  have ticket : env r.2.2 = 1 := by
    simpa only [circuit_norm] using congrArg (fun x : Inputs (ZMod p) => x.2.2) cells
  simp [endpoint, circuit_norm, head, address_zero, cursor, ticket]

/-- The generated seal's two physical walk occurrences. -/
theorem tableFor_walk (hints : List Bytes) (state : State (ZMod p)) (data : ProverData (ZMod p)) :
    (tableFor hints state data).interactionsWith channel.toRaw =
      [channel.pushedValue (endpoint 0 state.head), channel.pulledValue (endpoint (wordRows hints) 0)] := by
  rw [Table.interactionsWith_eq_filter, tableFor_ledger]
  simp [channel, stateChannel, Channel.toRaw, Channel.pushedValue, Channel.pulledValue]


end Seal

/-- The two physically generated tables close the entire cursor channel under raw LogUp,
using the real final pointer even when it exceeds the outgoing number of hints. -/
theorem tableFor_closed [Fact (2 ^ 17 < p)] {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) (fit : fits hints = true) (data : ProverData (ZMod p))
    (clock : BitVec 48) :
    let reader := tableFor store head hints fit data
    let terminal := Seal.tableFor hints (State.encode clock.toNat head store.size) data
    LogUpBalanced (reader.interactionsWith channel.toRaw ++ terminal.interactionsWith channel.toRaw) := by
  dsimp only
  intro msg
  rw [balanceOf_append, tableFor_walk_balance read, Seal.tableFor_walk]
  by_cases start : (toElements (endpoint (p := p) 0 (Address.ofNat head))).toArray = msg <;>
    by_cases finish : (toElements (endpoint (p := p) (wordRows hints) 0)).toArray = msg <;>
    simp [balanceOf, Channel.pushedValue, Channel.pulledValue, Interaction.signedMult, State.encode, start, finish]

end SP1Clean.HostHintSnapshot
