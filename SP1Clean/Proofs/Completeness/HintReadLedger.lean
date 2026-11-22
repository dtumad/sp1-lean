import SP1Clean.Proofs.Completeness.HintReadTables

/-! # Signed HINT_READ cursor ledger of the two generated tables

For each genuine call the first and final private cursor are the two handler endpoints. Adjacent
word rows cancel in chronological order. Regrouping by installed table and adding the actual
zero-weight padding preserves the signed sum for every serialized message key.
-/

namespace SP1Clean.TraceGen.HintReadTransfers
open Semantics Machine FormalModel.Shard HintQueue Soundness.Target
open Circuit Air.Flat HintReadWordChip

private abbrev F := ZMod SP1Prime
private abbrev Entry := Bool × RowInput F

/-- Signed private-cursor interactions of one physical word row, guarded by its activity. -/
def cursorValues (row : RowInput F) : List (Interaction F) :=
  [stateChannel.pulledIfValue row.2 row.1.previous, stateChannel.pushedIfValue row.2 row.1.next]

/-- The handler supplies the initial word cursor and receives the final one. A tape position
without a HINT_READ contributes no endpoints. -/
def endpoints (rows : List Entry) : List (Interaction F) :=
  match rows.head?, rows.getLast? with
  | some first, some last => [stateChannel.pushedValue first.2.1.previous, stateChannel.pulledValue last.2.1.next]
  | _, _ => []

/-- The chronological list of actual word-chain endpoints for all HINT_READ positions. -/
noncomputable def endpointLedger (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) :
    List (Interaction F) :=
  (List.finRange events.length).flatMap fun pos => endpoints ((rowsAt? image source events pos.val).getD [])

/-- Each nonempty logical batch in the endpoint ledger supplies exactly the two messages
used by its populated handler, for the displaced values and timestamps of its actual boundary rows. -/
theorem endpoints_eq_handler (store : Store) (head previousClock clock : ℕ) (exec : HostExecution)
    (bytes : Bytes) (length : bytes.length = exec.arg2.toNat) (span : HintReadSpan.Domain exec.arg1.toNat bytes.length)
    (frontier : AccessFrontier) (sail : SailState) :
    let request : Request := ⟨clock, head, exec.arg1.toNat, bytes⟩
    let handler := HostHintReadChip.populate (p := SP1Prime) store head previousClock clock exec
    endpoints (request.rows frontier sail) =
      [stateChannel.pushedValue handler.first, stateChannel.pulledValue handler.final] := by
  let request : Request := ⟨clock, head, exec.arg1.toNat, bytes⟩
  let index := bytes.length / 8
  let time (i : ℕ) := frontier (.ram (request.cell i))
  let old (i : ℕ) := (ramWord64? sail (BitVec.ofNat 64 (request.destination i))).getD 0
  have ⟨first, final⟩ := handler_endpoints store head previousClock clock exec bytes length span
    (time 0) (time index) (old 0) (old index)
  let entry (i : ℕ) : Entry := (request.last i, request.wordRow i (time i) (old i))
  change endpoints ((List.range (index + 1)).map entry) = _
  simp only [endpoints, List.head?_map, List.head?_range, Nat.succ_ne_zero, ↓reduceIte,
    List.getLast?_map, List.getLast?_range, Nat.add_sub_cancel, Option.map_some, entry]
  rw [first, final]

private def indicator (state : State F) (msg : Array F) : F := if (toElements state).toArray = msg then 1 else 0

private theorem cursor_delta (row : RowInput F) (msg : Array F) :
    balanceOf (cursorValues row) msg = row.2 * (indicator row.1.next msg - indicator row.1.previous msg) := by
  by_cases before : (toElements row.1.previous).toArray = msg <;>
    by_cases after : (toElements row.1.next).toArray = msg <;>
      simp [cursorValues, indicator, Channel.pulledIfValue, Channel.pushedIfValue,
        Interaction.signedMult, before, after, balanceOf]

private theorem endpoint_delta (first final : State F) (msg : Array F) :
    balanceOf [stateChannel.pushedValue first, stateChannel.pulledValue final] msg =
      indicator first msg - indicator final msg := by
  by_cases before : (toElements first).toArray = msg <;> by_cases after : (toElements final).toArray = msg <;>
    simp [indicator, Channel.pulledValue, Channel.pushedValue, Interaction.signedMult, before, after, balanceOf]

/-- All interior word cursors of the padded semantic write cancel, including a one-word read. -/
theorem Request.cursor_closed (request : Request) (frontier : AccessFrontier) (sail : SailState)
    (span : HintReadSpan.Domain request.address request.bytes.length) :
    let rows := request.rows frontier sail
    LogUpBalanced (endpoints rows ++ rows.flatMap (fun entry => cursorValues entry.2)) := by
  let row (i : ℕ) := request.wordRow i (frontier (.ram (request.cell i)))
    ((ramWord64? sail (BitVec.ofNat 64 (request.destination i))).getD 0)
  let entry (i : ℕ) : Entry := (request.last i, row i)
  have live (i : ℕ) : (row i).2 = 1 := rfl
  dsimp only
  intro msg
  have prefixSum (n : ℕ) (bound : n < wordCount request.bytes) :
      balanceOf ((List.range (n + 1)).flatMap (fun i => cursorValues (row i))) msg =
        indicator (row n).1.next msg - indicator (row 0).1.previous msg := by
    induction n with
    | zero => simp [cursor_delta, live]
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, balanceOf_append,
        ih (by omega), cursor_delta, live, one_mul]
      have connected : (row n).1.next = (row (n + 1)).1.previous := request.link n _ _ _ _ span bound
      rw [connected]
      abel
  let last := request.bytes.length / 8
  have ends : endpoints (request.rows frontier sail) =
      [stateChannel.pushedValue (row 0).1.previous, stateChannel.pulledValue (row last).1.next] := by
    change endpoints ((List.range (last+1)).map entry) = _
    simp [endpoints, List.head?_range, List.getLast?_range, entry]
  change balanceOf (endpoints (request.rows frontier sail) ++ _) msg = 0
  rw [ends, balanceOf_append, endpoint_delta]
  change _ + balanceOf (((List.range (last + 1)).map entry).flatMap (fun e => cursorValues e.2)) msg = 0
  rw [List.flatMap_map, show (fun i => cursorValues (entry i).2) = (fun i => cursorValues (row i)) from rfl,
    prefixSum last (by unfold last wordCount; omega)]
  abel

private theorem at_closed {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {event : ExecutionEvent} (present : events[cut]? = some event) :
    let rows := (rowsAt? image source events cut).getD []
    LogUpBalanced (endpoints rows ++ rows.flatMap (fun e => cursorValues e.2)) := by
  cases event with
  | ordinary => simp [rowsAt?, present, endpoints, LogUpBalanced, balanceOf]
  | syscall call =>
    by_cases read : call.rawCode = SyscallKind.hintRead.code
    · obtain ⟨current, _, frontier, cursor, _, bytes, _, _, built, _, queueBuilt, _, node, _, _, _, _,
        _, span, _⟩ := of_admissibleExecution execution present read
      simpa [rowsAt?, present, read, built, queueBuilt, node] using
        (Request.mk call.clock cursor.2 call.arg1.toNat bytes).cursor_closed frontier current.sail span
    · simp [rowsAt?, present, read, endpoints, LogUpBalanced, balanceOf]

private theorem combined_balance {α : Type} (positions : List α) (batch : α → List Entry) (msg : Array F)
    (closed : ∀ p ∈ positions, LogUpBalanced (endpoints (batch p) ++ (batch p).flatMap (fun e => cursorValues e.2))) :
    balanceOf (positions.flatMap (endpoints ∘ batch)) msg +
      balanceOf ((positions.flatMap batch).flatMap (fun e => cursorValues e.2)) msg = 0 := by
  induction positions with
  | nil => rfl
  | cons head tail ih =>
    have one := closed head List.mem_cons_self msg
    rw [balanceOf_append] at one
    have rest := ih (fun pos h => closed pos (List.mem_cons_of_mem _ h))
    simp only [List.flatMap_cons, Function.comp_apply, List.flatMap_append, balanceOf_append]
    linear_combination one + rest

private theorem padding_zero (n : ℕ) (msg : Array F) :
    balanceOf ((List.replicate n (0 : RowInput F)).flatMap cursorValues) msg = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, balanceOf_append, ih, cursor_delta]
    change 0 * _ + 0 = (0 : F)
    simp

private theorem split_sum (entries : List Entry) (msg : Array F) :
    balanceOf ((selected false entries).flatMap cursorValues) msg +
      balanceOf ((selected true entries).flatMap cursorValues) msg =
      balanceOf (entries.flatMap (fun e => cursorValues e.2)) msg := by
  induction entries with
  | nil => simp [selected, balanceOf]
  | cons entry rest ih =>
    rcases entry with ⟨flag, row⟩
    cases flag <;>
      simp only [selected, List.filter_cons, beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false,
        ↓reduceIte, List.map_cons, List.flatMap_cons, balanceOf_append] at ih ⊢ <;>
      linear_combination ih

/-- The actual physical cursor-channel occurrences of both generated tables close exactly
against the call endpoints, at every message key. Heights are derived from the same execution. -/
theorem tables_cursor_closed {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (data : ProverData F) :
    let entries := history image source events
    ∃ nextHeight lastHeight,
      let next := wordTable false entries data nextHeight
      let last := wordTable true entries data lastHeight
      next.Constraints ∧ next.Guarantees ∧ last.Constraints ∧ last.Guarantees ∧
        LogUpBalanced ((endpointLedger image source events ++ next.interactionsWith stateChannel.toRaw) ++
          last.interactionsWith stateChannel.toRaw) := by
  let entries := history image source events
  obtain ⟨nextHeight, nextConstraints, nextGuarantees⟩ := tables_of_admissibleExecution execution false data
  obtain ⟨lastHeight, lastConstraints, lastGuarantees⟩ := tables_of_admissibleExecution execution true data
  refine ⟨nextHeight, lastHeight, nextConstraints, nextGuarantees, lastConstraints, lastGuarantees, ?_⟩
  intro msg
  have physical (last : Bool) (height) :
      balanceOf ((wordTable last entries data height).interactionsWith stateChannel.toRaw) msg =
        balanceOf ((selected last entries).flatMap cursorValues) msg := by
    rw [wordTable_cursors]
    change balanceOf (((selected last entries) ++ _).flatMap cursorValues) msg = _
    rw [List.flatMap_append, balanceOf_append, padding_zero, add_zero]
  have sum := combined_balance (List.finRange events.length)
    (fun i => (rowsAt? image source events i.val).getD []) msg (fun i _ => at_closed execution (List.getElem?_eq_getElem i.isLt))
  change balanceOf (endpointLedger image source events) msg +
    balanceOf (entries.flatMap (fun e => cursorValues e.2)) msg = 0 at sum
  rw [balanceOf_append, balanceOf_append, physical, physical, add_assoc, split_sum]
  exact sum

end SP1Clean.TraceGen.HintReadTransfers
