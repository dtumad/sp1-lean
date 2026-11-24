import SP1Clean.Proofs.Completeness.MixedMemoryValues
import SP1Clean.Proofs.Completeness.MemoryRecordExecution

/-! # Handoffs on the full generated mixed Memory tape

Every compiled event consumes the true incoming Memory records, including aliased operands,
register refreshes, and the padded HINT_READ destinations. The complete run starts at the
boundary's genesis frontier.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Semantics Machine FormalModel.Shard Soundness.Target MemoryHistoryAccess

private abbrev F := ZMod SP1Prime

private theorem register_frontier_ram (f : AccessFrontier) (base : ℕ) (call : CoreSyscallEvent) (cell : RamCell) :
    advancePlan f base (syscallRegisterPlan call) (.ram cell) = f (.ram cell) := by
  simp [advancePlan, syscallRegisterPlan, advanceFrontier, Function.update_of_ne]

private theorem hint_request {request : HintReadTransfers.Request} {frontier final : AccessFrontier}
    {source target : SailState} {store : HintQueue.Store} (span : HintReadSpan.Domain request.address request.bytes.length)
    (atWord : ∀ j < HintQueue.wordCount request.bytes, request.WordAt j frontier final source target store) :
    let words := (request.rows frontier source).map fun e => hint e.2
    (words.map MemoryHistoryAccess.loc).Nodup ∧ ∀ a ∈ words, (∃ cell, a.loc = .ram cell) ∧
      a.previous = frontier a.loc ∧ some a.pulled = locContent source a.loc ∧
      a.current = final a.loc ∧ some a.pushed = locContent target a.loc ∧ a.current = request.clock + 1 := by
  intro words
  have atIndex (j : ℕ) (pos : j < HintQueue.wordCount request.bytes) :
      let r := hint ((request.rows frontier source)[j]'(by rwa [request.rows_length])).2
      r.loc = .ram (request.cell j) ∧ r.loc.busAddress = request.destination j ∧
      r.previous = frontier r.loc ∧ r.current = final r.loc ∧ locContent source r.loc = some r.pulled ∧
      locContent target r.loc = some r.pushed ∧ r.current = request.clock + 1 :=
    hint_word_endpoints span pos (atWord j pos) (List.getElem?_eq_getElem _)
  constructor
  · apply List.Nodup.of_map MemLoc.busAddress
    have keys : (words.map MemoryHistoryAccess.loc).map MemLoc.busAddress =
        (HintQueue.wordWrites request.address request.bytes).map Prod.fst := by
      apply List.ext_getElem
      · simp [words, request.rows_length, HintQueue.wordWrites_length]
      · intro j left right
        have pos : j < HintQueue.wordCount request.bytes := by simpa [words, request.rows_length] using left
        simpa only [words, List.getElem_map, HintQueue.wordWrites, List.getElem_range, HintReadTransfers.Request.destination] using (atIndex j pos).2.1
    rw [keys]
    exact HintQueue.wordWrites_addresses_nodup _ _
  · intro a occurs
    obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp occurs
    obtain ⟨j, inside, rfl⟩ := List.mem_iff_getElem.mp mem
    have pos : j < HintQueue.wordCount request.bytes := by simpa only [request.rows_length] using inside
    obtain ⟨whereAt, _, prior, pushed, old, value, clock⟩ := atIndex j pos
    exact ⟨⟨_, whereAt⟩, prior, old.symm, pushed, value.symm, clock⟩

private theorem syscall_word_transfers {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    {before next : ExecutionState} {incoming : AccessFrontier}
    (step : ExecutionStep (policy SP1Prime image) image.program before (.syscall call) next)
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (before, incoming))
    (nextCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (cut + 1) =
      some (next, syscallFrontier incoming before.clock call)) :
    let words := ((HintReadTransfers.rowsAt? image source events cut).getD []).map fun entry => hint entry.2
    Transfers (advancePlan incoming before.clock (syscallRegisterPlan call)) (syscallFrontier incoming before.clock call)
      (afterRegisters before.sail next.sail) (locContent next.sail)
      words ∧ ∀ a ∈ words, a.previous = incoming a.loc ∧ a.current = before.clock + 1 := by
  intro words
  have records : (words.map MemoryHistoryAccess.loc).Nodup ∧ ∀ a ∈ words, (∃ cell, a.loc = .ram cell) ∧
      a.previous = incoming a.loc ∧ some a.pulled = locContent before.sail a.loc ∧
      a.current = syscallFrontier incoming before.clock call a.loc ∧ some a.pushed = locContent next.sail a.loc ∧ a.current = call.clock + 1 := by
    by_cases read : call.rawCode = SyscallKind.hintRead.code
    · obtain ⟨current, final, frontier, cursor, last, bytes, rest, tail, reached, doneAt, stored, _, node, _, _, _, _, _, span, atWord⟩ :=
        HintReadTransfers.of_admissibleExecution run present read
      cases Option.some.inj (atCut.symm.trans reached)
      cases Option.some.inj (nextCut.symm.trans doneAt)
      let req : HintReadTransfers.Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
      have found : HintReadTransfers.rowsAt? image source events cut = some (req.rows incoming before.sail) := by
        simp [HintReadTransfers.rowsAt?, present, read, atCut, stored, node, req]
      simpa only [words, found, Option.getD_some] using hint_request (request := req) span atWord
    · simp [words, HintReadTransfers.rowsAt?, present, read]
  refine ⟨?_, fun a mem => ⟨(records.2 a mem).2.1, ?_⟩⟩
  swap
  · have eq : call.clock = before.clock := step.startsAt
    rw [← eq]; exact (records.2 a mem).2.2.2.2.2
  apply transfers_disjoint records.1
  · intro a mem
    obtain ⟨⟨cell, located⟩, prior, old, clock, posted, _⟩ := records.2 a mem
    rw [located] at prior old clock posted ⊢
    exact ⟨by rw [register_frontier_ram]; exact prior, old, clock, posted⟩
  · intro loc fresh
    cases loc with
    | reg => rfl
    | ram cell =>
      have outside : ¬(call.rawCode = SyscallKind.hintRead.code ∧ call.arg1.toNat / 8 ≤ cell.toNat ∧
          cell.toNat < call.arg1.toNat / 8 + (call.arg2.toNat / 8 + 1)) := by
        rintro ⟨read, lo, hi⟩
        obtain ⟨entry, mem, key⟩ := hint_at_cell run present read lo hi
        exact fresh _ (List.mem_map_of_mem mem) key
      apply Prod.ext
      · simp [register_frontier_ram, syscallFrontier, outside]
      · exact (syscall_ram_frontier_zero step (fun _ => 0) cell (by simp [syscallFrontier, outside])).2.symm

private theorem strict_schedule {base : ℕ} {s : AccessSchedule}
    (ordinary : ∀ a ∈ s.stampedTouches, a.previous < a.current base)
    (bumped : ∀ b ∈ s.memoryBumps, b.WellFormed) :
    ∀ a ∈ ofAccessSchedule base s, a.previous < a.current := by
  intro a occurs
  obtain ⟨slot, found, member⟩ := List.mem_flatMap.mp occurs
  rcases List.mem_append.mp member with bump | normal
  · obtain ⟨e, someBump, rfl⟩ := List.mem_map.mp bump
    exact (bumped _ (List.mem_filterMap.mpr ⟨slot, found, Option.mem_toList.mp someBump⟩)).increases
  · cases List.mem_singleton.mp normal
    exact ordinary _ (List.mem_map_of_mem found)

/-- At each actual mixed CPU event all displaced clocks and incoming words are authentic. Each
original Memory row, including every refresh and HINT word, strictly advances its own location. -/
theorem batch_records {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (i : Fin rows.length) {before next : ExecutionState} {incoming outgoing : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events i.val = some (before, incoming))
    (nextCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (i.val + 1) = some (next, outgoing)) :
    Transfers incoming outgoing (locContent before.sail) (locContent next.sail) (batch image source events rows i) ∧
      ∀ r ∈ batch image source events rows i, r.previous < r.current := by
  obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
  have present := List.getElem?_eq_getElem (i.isLt.trans_eq length)
  generalize eventEq : events[i.val] = event at present
  obtain ⟨current, f, path, actualCut, bounded⟩ := admissibleExecution_mixedAccessPrefix run i.val
  cases Option.some.inj (atCut.symm.trans actualCut)
  obtain ⟨now, prior, later, recovered, replay, emitted⟩ := routeMixedRows?_at routed present
  cases Option.some.inj (atCut.symm.trans recovered)
  cases event with
  | ordinary =>
    obtain ⟨s, n, view, row, earlier, step, projected, made, _, _, facts⟩ := admissibleExecution_compile_at run present incoming
    cases Option.some.inj (path.symm.trans earlier)
    cases Option.some.inj (replay.symm.trans step.replay)
    obtain ⟨view', row', projected', compiled', found⟩ := emitted
    cases Option.some.inj (projected.symm.trans projected')
    cases Option.some.inj (made.symm.trans compiled')
    have advanced : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (i.val + 1) =
        some (later, row.nextFrontier) := by
      rw [mixedAccessPrefix_succ _ _ _ _ present, atCut, Option.bind_some]
      simp [mixedAccessStep, emitMixedAccessStep?, step.replay, projected, made]
    cases Option.some.inj (advanced.symm.trans nextCut)
    have noWords : HintReadTransfers.rowsAt? image source events i.val = some [] := by simp [HintReadTransfers.rowsAt?, present]
    simp only [batch, Fin.getElem_fin, (List.getElem?_eq_some_iff.mp found).2, noWords, Option.getD_some, List.map_nil, List.append_nil, cpu,
      (compileInstructionEvent?_coordinates made).1]
    have frame := run.1.frame_prefix path
    refine ⟨?_, strict_schedule (facts bounded).1 (facts bounded).2.1⟩
    rw [compileInstructionEvent?_schedule made, compileInstructionEvent?_nextFrontier made]
    exact transfers_of_schedule (ordinary_plan_values step frame.1 frame.2.1 ((run.2.1 _ _ _ present path).2 rfl)
      projected (compileInstructionEvent?_accessPlan_generated projected made)) _ _
  | syscall call =>
    obtain ⟨s, f, n, _, cut, step, advanced, _, _, _, _, strict, bumps⟩ := admissibleExecution_syscall_from_prefix run present
    cases Option.some.inj (atCut.symm.trans cut)
    cases Option.some.inj (advanced.symm.trans nextCut)
    obtain ⟨words, clocks⟩ := syscall_word_transfers run present step atCut advanced
    simp only [batch, Fin.getElem_fin, (List.getElem?_eq_some_iff.mp emitted).2, cpu]
    refine ⟨(transfers_of_schedule (syscall_register_values step) _ _).append words, ?_⟩
    intro r mem
    rcases List.mem_append.mp mem with reg | hint
    · exact strict_schedule strict bumps r reg
    · obtain ⟨priorTime, postedTime⟩ := clocks r hint
      rw [priorTime, postedTime]
      exact bounded r.loc

private theorem prefix_records {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {current : ExecutionState} {f : AccessFrontier}
    (reached : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, f)) :
    let tape := ((List.finRange rows.length).take cut).flatMap (batch image source events rows)
    Transfers AccessFrontier.initial f (locContent source.realize.sail) (locContent current.sail) tape ∧
      ∀ a ∈ tape, a.previous < a.current := by
  induction cut generalizing current f with
  | zero => cases reached; exact ⟨Transfers.nil _ _, by simp⟩
  | succ cut ih =>
    by_cases inRows : cut < rows.length
    · let i : Fin rows.length := ⟨cut, inRows⟩
      obtain ⟨before, incoming, _, prior, _⟩ := admissibleExecution_mixedAccessPrefix run cut
      obtain ⟨first, strict⟩ := ih prior
      obtain ⟨later, advances⟩ := batch_records run routed i prior reached
      dsimp only
      rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using inRows),
        List.flatMap_append, List.flatMap_singleton]
      have eq : (List.finRange rows.length)[cut]'(by simpa using inRows) = i := Fin.ext (by simp [i])
      rw [eq]
      exact ⟨first.append later, fun a mem => (List.mem_append.mp mem).elim (strict a) (advances a)⟩
    · obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
      have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
      have ended : events.length ≤ cut := by omega
      have past : (List.finRange rows.length).length ≤ cut := by simpa using Nat.le_of_not_gt inRows
      dsimp only
      rw [List.take_of_length_le (Nat.le_succ_of_le past), ← List.take_of_length_le past]
      apply ih
      simpa only [mixedAccessPrefix, List.take_of_length_le (Nat.le_succ_of_le ended), List.take_of_length_le ended] using reached

/-- The complete generated tape hands off every source Memory record to its actual outgoing
frontier and Sail word. Every occurrence strictly advances the clock at that location. -/
theorem records {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows) :
    ∃ final, mixedAccessPrefix (policy SP1Prime image) image.program source.realize events events.length = some (target.realize, final) ∧
      Transfers AccessFrontier.initial final (locContent source.realize.sail) (locContent target.realize.sail) (stream image source events rows) ∧
      ∀ r ∈ stream image source events rows, r.previous < r.current := by
  obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
  obtain ⟨s, f, path, reached, _⟩ := admissibleExecution_mixedAccessPrefix run events.length
  have terminal : s = target.realize := Option.some.inj (path.symm.trans (by simpa only [executionTrajectory, List.take_length] using run.1.2.replay))
  subst s
  refine ⟨f, reached, ?_⟩
  have covers : (List.finRange rows.length).length ≤ events.length := by simp [length]
  have flat : stream image source events rows = (List.finRange rows.length).flatMap (batch image source events rows) := rfl
  rw [flat]
  simpa only [List.take_of_length_le covers] using prefix_records run routed reached

/-- The boundary compiler's genesis and adjacent handoff obligations follow from the native
execution itself, including high-window stutters and the actual ordered HINT_READ words. -/
theorem record_chronology {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows) :
    MemoryRecordChronology (stream image source events rows) ∧ ∀ r ∈ stream image source events rows, r.previous < r.current := by
  obtain ⟨_, _, transfers, strict⟩ := records run routed
  exact ⟨transfers.chronology, strict⟩


end SP1Clean.TraceGen.MixedMemoryHistory
