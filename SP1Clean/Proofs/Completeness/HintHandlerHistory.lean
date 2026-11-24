import SP1Clean.Proofs.Completeness.HintQueueReaders
import SP1Clean.Proofs.Completeness.WriteAllocationStore
import SP1Clean.Proofs.Chips.HostHintLengthChip.Guarded
import SP1Clean.Proofs.Chips.HostHintReadChip.Guarded

/-! # Building the three guarded hint handlers from mixed execution

A row uses the actual dispatcher result, the persistent queue at that event, and the
preceding queue clock shared with allocating WRITEs. Transfer words come from the same
prefix of the original mixed tape.
-/

namespace SP1Clean.TraceGen.HintHandlers

open Circuit Air.Flat Semantics HintQueue Machine FormalModel.Shard
private abbrev F := ZMod SP1Prime

/-- A single active physical receiver input before distribution to the three demand tables. -/
inductive Row where
  /-- HINT_LEN and its physical routing bit. -/
  | length (empty : Bool) (input : HostHintLengthChip.Inputs F)
  /-- HINT_READ, including its mandatory final padded word. -/
  | read (input : HostHintReadChip.Inputs F)

/-- The completeness condition on the actual active input of its selected circuit. -/
def Row.Honest : Row → Prop
  | .length empty input => HostHintLengthChip.Spec empty input
  | .read input => HostHintReadChip.ProverAssumptions input

/-- Immutable metadata read at a handler, preserving the zero-head case. -/
def Row.nodes : Row → List (NodeRecord F)
  | .length true _ => []
  | .length false input => [input.node]
  | .read input => [input.node]

/-- Independently of transfer-step reads, the HINT_READ header reads the final stored word. -/
def Row.words : Row → List (WordRecord F)
  | .length _ _ => []
  | .read input => [input.endStep.word]

/-- Route a successful call from its original mixed execution position. -/
noncomputable def at? (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (cut : Nat) : Option Row := do
  let .syscall call ← events[cut]? | none
  let hostPolicy := policy SP1Prime image
  let current ← executionTrajectory hostPolicy image.program source.realize events cut
  let executed ← current.host.run hostPolicy (.ofSail current.sail)
  let cursor ← storeAfter? hostPolicy image.program source.realize (events.take cut) (ofList source.host.io.hints)
  let prev := (events.take cut).foldl WriteAllocation.advanceQueueClock 0
  if call.rawCode = SyscallKind.hintRead.code then
    return .read (HostHintReadChip.populate cursor.1 cursor.2 prev call.clock executed)
  else if call.rawCode = SyscallKind.hintLength.code then
    return .length (decide (cursor.2 = 0)) (HostHintLengthChip.populate cursor.1 cursor.2 prev call.clock executed)
  else none

/-- Chronological handler headers before splitting into their original physical slots. -/
noncomputable def history (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) : List Row :=
  (List.finRange events.length).filterMap fun cut => at? image source events cut.val

/-- Typed read requests of an original transfer step. -/
def transferWord (row : Bool × HintReadWordChip.RowInput F) : WordRecord F := (row.2.1.step row.1).word

private theorem head_node {store : Store} {ptr : Nat} {bytes : Bytes} {rest : List Bytes}
    (represented : Represents store ptr (bytes :: rest)) : ∃ node, node? store ptr = some node := by
  cases represented with | cons found _ _ => exact ⟨_, found⟩

private theorem demand_eq {q : HintQueueReaders.Demand} {nodes words}
    (hn : q.nodes = nodes) (hw : q.words = words) : q = ⟨nodes, words⟩ := by
  cases q
  cases hn
  cases hw
  rfl

/-- Independent header and transfer demands reproduce every original semantic immutable query
at this cut. A non-hint event produces no header or transfer rows. -/
theorem at_complete {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {cut : Nat} {event : ExecutionEvent} (present : events[cut]? = some event) :
    let selected := at? image source events cut
    let transfers := (HintReadTransfers.rowsAt? image source events cut).getD []
    (∀ row ∈ selected.toList, row.Honest) ∧
      HintQueueReaders.at? image source events cut =
        some ⟨selected.toList.flatMap Row.nodes, selected.toList.flatMap Row.words ++ transfers.map transferWord⟩ := by
  dsimp only
  obtain ⟨reached, cursor, _, path, stored, rep, _, headBound, storeBound, _⟩ := admissibleExecution_hintInventory run cut
  cases event with
  | ordinary =>
    simp [at?, HintQueueReaders.at?, present, stored, HintQueueReaders.atCursor, HintReadTransfers.rowsAt?]
  | syscall call =>
    obtain ⟨current, frontier, next, trajectory, compiled, step, _, _, phase, fits, _⟩ :=
      admissibleExecution_syscall_from_prefix run present
    obtain rfl : reached = current := Option.some.inj (path.replay.symm.trans trajectory)
    cases step with
    | syscall success =>
      obtain ⟨pc, exec, _, _, executed, _, _, eventEq⟩ := HostState.step_observations success
      have clock : call.clock = reached.clock := by rw [eventEq]; rfl
      let prev := (events.take cut).foldl WriteAllocation.advanceQueueClock 0
      have ordered : prev < call.clock := by
        have order := WriteAllocation.queue_clock_before path 0 (Or.inl rfl)
        change reached.clock % 8 = 1 at phase
        rw [clock]
        dsimp only [prev]
        omega
      have small : call.clock < 2^48 := by omega
      simp only [at?, HintQueueReaders.at?, present, trajectory, executed, stored, Option.bind_eq_bind,
        Option.bind_some, pure]
      by_cases read : call.rawCode = SyscallKind.hintRead.code
      · have kind : exec.kind = .hintRead := SyscallKind.code_injective (by simpa only [eventEq, HostExecution.toEvent] using read)
        have valid := HostHintReadChip.populate_of_run (p := SP1Prime) cursor.1 cursor.2 prev call.clock exec reached.host
          (policy SP1Prime image) (.ofSail reached.sail) executed kind rep storeBound (by rfl) (by rfl) small ordered
        have effect := ((HostState.run_eq_some_iff ..).mp executed).2.2.2.2.2
        rw [kind] at effect
        obtain ⟨bytes, rest, head, _⟩ := (HostState.execute_hintRead_iff ..).mp effect
        rw [head] at rep
        obtain ⟨node, found⟩ : ∃ n, node? cursor.1 cursor.2 = some n := head_node rep
        obtain ⟨nodes, words⟩ := HintQueueReaders.read_demand cursor call read prev exec found frontier reached.sail
        simp only [ite_eq_left read, Option.toList_some, List.mem_cons, List.not_mem_nil, or_false,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, Row.nodes, Row.words, List.cons_append, List.nil_append]
        refine ⟨fun _ eq => eq ▸ valid.1, ?_⟩
        apply congrArg some
        refine demand_eq nodes ?_
        rw [show transferWord = (fun e => (e.2.1.step e.1).word) from rfl]
        simpa only [HintReadTransfers.rowsAt?, present, read, ↓reduceIte, compiled, stored, found,
            Option.bind_eq_bind, Option.bind_some, pure, Option.getD_some, prev] using words
      · by_cases len : call.rawCode = SyscallKind.hintLength.code
        · have kind : exec.kind = .hintLength := SyscallKind.code_injective (by simpa only [eventEq, HostExecution.toEvent] using len)
          have valid := HostHintLengthChip.populate_spec_of_run (p := SP1Prime) cursor.1 cursor.2 prev call.clock
            exec reached.host (policy SP1Prime image) (.ofSail reached.sail) executed kind rep (headBound.trans_lt storeBound) small ordered
          obtain ⟨nodes, words⟩ := HintQueueReaders.length_demand cursor call len prev exec rep
          simp only [ite_eq_right read, ite_eq_left len, Option.toList_some, List.mem_cons, List.not_mem_nil, or_false,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Row.words, List.nil_append]
          refine ⟨fun _ eq => eq ▸ valid, ?_⟩
          apply congrArg some
          apply demand_eq
          · rw [nodes]
            by_cases z : cursor.2 = 0 <;> simp [z, Row.nodes, prev]
          · simpa only [HintReadTransfers.rowsAt?, present, read, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_some, pure, Option.getD_some, List.map_nil] using words
        · simp [read, len, HintQueueReaders.atCursor, HintReadTransfers.rowsAt?, present]

/-- All generated headers meet their actual active circuit assumptions. -/
theorem history_honest {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    ∀ row ∈ history image source events, row.Honest := by
  intro row member
  obtain ⟨cut, _, selected⟩ := List.mem_filterMap.mp member
  have atCut := at_complete run (List.getElem?_eq_getElem cut.isLt)
  apply atCut.1 row
  simp [selected]

/-- Nodes are in chronological call order. Word requests from all headers and all original
transfer rows permute the chronological immutable demand, including each duplicated final word. -/
theorem history_reads {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (history image source events).flatMap Row.nodes =
      (HintQueueReaders.history image source events).flatMap HintQueueReaders.Demand.nodes ∧
    ((history image source events).flatMap Row.words ++
      (HintReadTransfers.history image source events).map transferWord).Perm
      ((HintQueueReaders.history image source events).flatMap HintQueueReaders.Demand.words) := by
  let heads (i : Fin events.length) := (at? image source events i.val).toList
  let words (i : Fin events.length) := ((HintReadTransfers.rowsAt? image source events i.val).getD []).map transferWord
  let queries (i : Fin events.length) : HintQueueReaders.Demand :=
    ⟨(heads i).flatMap Row.nodes, (heads i).flatMap Row.words ++ words i⟩
  have demand : HintQueueReaders.history image source events = (List.finRange events.length).map queries := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro i _
    exact (at_complete run (List.getElem?_eq_getElem i.isLt)).2
  rw [demand]
  simp only [history, List.filterMap_eq_flatMap_toList, HintReadTransfers.history, List.flatMap_assoc,
    List.map_flatMap, List.flatMap_map]
  exact ⟨rfl, List.flatMap_append_perm _ (fun i => (heads i).flatMap Row.words) words⟩

/-- A native shard pays the full 264-tick cost for every selected receiver. Each original
handler bucket therefore fits a power-of-two height of 65,536. -/
theorem history_bound {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (history image source events).length ≤ 2^16 := by
  have count (ps : List (Fin events.length)) :
      264 * (ps.filterMap (fun i => at? image source events i.val)).length ≤
        (ps.map (fun i => events[i.val].duration)).sum := by
    induction ps with
    | nil => simp
    | cons i rest ih =>
      have present := List.getElem?_eq_getElem (l := events) i.isLt
      cases he : events[i.val] with
      | ordinary =>
        rw [he] at present
        have absent : at? image source events i.val = none := by simp only [at?, present, Option.bind_eq_bind, Option.bind_some]
        simp only [List.filterMap_cons, absent, List.map_cons, List.sum_cons, he, ExecutionEvent.duration_ordinary]
        omega
      | syscall call =>
        cases h : at? image source events i.val <;>
          simp only [List.filterMap_cons, h, List.length_cons, List.map_cons, List.sum_cons, he, ExecutionEvent.duration_syscall] <;> omega
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  change (events.map ExecutionEvent.duration).sum ≤ 2^24 at ticks
  have total := congrArg (fun es => (es.map ExecutionEvent.duration).sum) (List.map_getElem_finRange events)
  simp only [List.map_map, Function.comp_def] at total
  have paid := count (List.finRange events.length)
  rw [total] at paid
  change (List.filterMap _ _).length ≤ 2^16
  omega

end SP1Clean.TraceGen.HintHandlers
