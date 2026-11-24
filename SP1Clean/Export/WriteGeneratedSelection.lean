import SP1Clean.Export.WriteBoundaryDemand
import SP1Clean.Export.WriteGeneratedRamSources

/-! # Classifying a selected predecessor in the generated physical tables

The four cases use the actual released instruction bucket, ECALL table, padded HINT_READ
word table, and register refresh table. Each case retains the exact published readback.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

/-- A positive physical predecessor of the chosen source: its actual originating input and bucket,
at the clocks used by the registered compiler. -/
inductive GeneratedPredecessor (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (rows : List MixedCompiledRow) : Source → Readback F → Prop
  | ordinary {located : LocatedTransition} {view : SP1TransitionView} {f : AccessFrontier}
      {base : ℕ} {row : CompiledInstructionEvent} {touch : StampedTouch}
      (projected : projectSP1Transition? image.program located = some view)
      (made : compileInstructionEvent? view f base = some row) (phase : activeClockPhase base)
      (used : touch ∈ row.stamped) (legal : touch.touch.loc.CanonicalAddress)
      (bucket : row.routed.event ∈ EventBuckets.ofChronological (rows.filterMap MixedCompiledRow.ordinaryObservation?) row.routed.id)
      (valid : row.routed.id.Valid row.routed.event) :
      GeneratedPredecessor image source events rows (.ordinary row.routed.id) (compiledReadback base (.ofStamped base touch))
  | ecall {f : AccessFrontier} {call : CoreSyscallEvent} {a : MemoryHistoryAccess}
      (used : MixedCompiledRow.syscall f call.clock call ∈ rows) (phase : activeClockPhase call.clock)
      (operand : a ∈ MixedMemoryHistory.instruction (.syscall f call.clock call)) :
      GeneratedPredecessor image source events rows (.host .ecall) (compiledReadback call.clock a)
  | hint {entry : Bool × HintReadWordChip.RowInput F} (used : entry ∈ HintReadTransfers.history image source events) :
      GeneratedPredecessor image source events rows (.host (.word entry.1))
        (AccessSupply.atClock (entry.2.1.ram.clk_high, entry.2.1.ram.clockLow) entry.2.1.ram.prior)
  | refresh {e : MemoryBumpEvent} (used : e ∈ MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput)) :
      GeneratedPredecessor image source events rows .refresh (InstalledAssembly.refreshEventReceipt e)

private theorem refresh_eq (e : MemoryBumpEvent) (valid : e.WellFormed) :
    InstalledAssembly.refreshEventReceipt e = compiledReadback e.currTs (.ofMemoryBump e) := by
  let row := memoryBumpCols (p := SP1Prime) e
  let current := Soundness.MemoryBumpChip.pushedMessage row
  change AccessSupply.atClock (current.clk_high, current.clk_low) (Soundness.MemoryBumpChip.pulledMessage row) = _
  obtain ⟨prior, posted⟩ := InstalledAssembly.refresh_transfers e valid
  change Soundness.MemoryBumpChip.pulledMessage row = _ at prior
  change current = _ at posted
  rw [prior, posted]
  rfl

private theorem hint_eq {request : HintReadTransfers.Request} {j : ℕ} {f g : AccessFrontier}
    {s t : SailState} {store : HintQueue.Store} {entry : Bool × HintReadWordChip.RowInput F}
    (span : HintReadSpan.Domain request.address request.bytes.length) (pos : j < HintQueue.wordCount request.bytes)
    (atWord : request.WordAt j f g s t store) (found : (request.rows f s)[j]? = some entry) :
    let ram := entry.2.1.ram
    AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior = compiledReadback request.clock (MixedMemoryHistory.hint entry.2) := by
  have fields := MixedMemoryHistory.hint_word_endpoints span pos atWord found
  obtain ⟨actual, _, _, _, _, stamp, _⟩ := atWord
  cases Option.some.inj (actual.symm.trans found)
  let dest := request.destination j
  let old := (ramWord64? s (BitVec.ofNat 64 dest)).getD 0
  let r := request.wordRow j (f (.ram (request.cell j))) old
  let a := MixedMemoryHistory.hint r
  have key : a.loc.busAddress = dest := fields.2.1
  have time : a.previous = f (.ram (request.cell j)) := stamp
  have value : wordOfNat (p := SP1Prime) a.pulled.toNat = r.1.ram.prior.value := by
    apply Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (Target.isU64_bitVecToWord _)
    rw [toBitVec64_wordOfNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  have recordEq : a.pulledEntry.toMemoryMsg (p := SP1Prime) = r.1.ram.prior := by
    simp only [MemoryHistoryAccess.pulledEntry, MemoryHistoryAccess.busAddress, MemRecordEntry.toMemoryMsg, time, key, value]
    rfl
  change AccessSupply.atClock (r.1.ram.clk_high, r.1.ram.clockLow) r.1.ram.prior = compiledReadback request.clock a
  rw [compiledReadback, recordEq]
  apply congrArg (fun pair => AccessSupply.atClock pair r.1.ram.prior)
  apply Prod.ext _ (clkLow_eq request.clock 0)
  change (cpuStateCols (p := SP1Prime) request.clock 0).clk_high = _
  rw [cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow]

private theorem hint_origin {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {i : ℕ} {before : ExecutionState} {f : AccessFrontier}
    (prefixAt : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events i = some (before, f))
    {event : ExecutionEvent} (atEvent : events[i]? = some event)
    {entry : Bool × HintReadWordChip.RowInput F} (used : entry ∈ (HintReadTransfers.rowsAt? image source events i).getD []) :
    let ram := entry.2.1.ram
    AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior = compiledReadback before.clock (MixedMemoryHistory.hint entry.2) := by
  cases event with
  | ordinary => simp [HintReadTransfers.rowsAt?, atEvent] at used
  | syscall call =>
    by_cases isRead : call.rawCode = SyscallKind.hintRead.code
    · obtain ⟨s, n, fr, cursor, last, bytes, rest, tail, reached, _, stored, _, node, _, _, _, _, clock, span, words⟩ :=
        HintReadTransfers.of_admissibleExecution run atEvent isRead
      cases Option.some.inj (prefixAt.symm.trans reached)
      let request : HintReadTransfers.Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
      have grouped : HintReadTransfers.rowsAt? image source events i = some (request.rows f before.sail) := by
        simp [HintReadTransfers.rowsAt?, atEvent, isRead, prefixAt, stored, node, request]
      rw [grouped, Option.getD_some] at used
      obtain ⟨j, found⟩ := List.mem_iff_getElem?.mp used
      have pos := (List.getElem?_eq_some_iff.mp found).1
      rw [request.rows_length] at pos
      rw [clock]
      exact hint_eq span pos (words j pos) found
    · simp [HintReadTransfers.rowsAt?, atEvent, isRead] at used

/-- An emitted predecessor is funded by one of the exact four generated physical row families.
Released jump-link encoding is used only to establish the ordinary event's genuine row validity. -/
theorem classify_predecessor {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {read : Read F} (chosen : WriteBoundaryBuild.CompiledPredecessor image source events rows cut read) :
    ∃ id receipt, GeneratedPredecessor image source events rows id receipt ∧ Counted.Covers receipt read := by
  obtain ⟨i, before, a, request, _, _, path, member, legal, lower, upper, fits, encoded⟩ := chosen
  obtain ⟨allRows, same, size⟩ := admissibleExecution_routeMixedRows run.1
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
  have inside : i.val < events.length := i.isLt.trans_eq length
  have active := List.getElem?_eq_getElem inside
  generalize eventEq : events[i.val] = event at active
  obtain ⟨current, f, actualPath, atCut, _⟩ := admissibleExecution_mixedAccessPrefix run.1 i.val
  cases Option.some.inj (path.symm.trans actualPath)
  obtain ⟨_, _, later, compared, replay, emitted⟩ := routeMixedRows?_at routed active
  cases Option.some.inj (atCut.symm.trans compared)
  have phase := (run.1.2.1 i.val before event active path).1
  have covered := compiledReadback_covers legal lower upper fits
  rw [← encoded] at covered
  rcases List.mem_append.mp member with cpu | word
  · have split : (MixedMemoryHistory.cpu rows[i]).Perm
        (rows[i].bumpInput.refreshes.map MemoryHistoryAccess.ofMemoryBump ++ MixedMemoryHistory.instruction rows[i]) := by
      simpa only [List.flatMap_singleton, List.map_singleton, MixedBumpInput.memoryRows] using MixedMemoryHistory.cpu_partition [rows[i]]
    rcases List.mem_append.mp (split.mem_iff.mp cpu) with bump | operand
    · obtain ⟨e, occurs, rfl⟩ := List.mem_map.mp bump
      have origin : e ∈ MixedBumpInput.memoryRows (rows.map MixedCompiledRow.bumpInput) :=
        List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem (List.getElem_mem ..), occurs⟩
      obtain ⟨inputs, generated, _, _, _, honest, _⟩ := admissibleExecution_mixedBumpInventory run.1
      have eq : inputs = rows.map MixedCompiledRow.bumpInput := Option.some.inj (generated.symm.trans (by simp [routeBumpInputs?, routed]))
      subst inputs
      have valid := honest e origin
      obtain ⟨start, finish, fromPath, _, _, window⟩ := MixedMemoryHistory.batch_values run.1 routed i
      cases Option.some.inj (path.symm.trans fromPath)
      have starts := (window _ member).1
      change before.clock < e.currTs at starts
      refine ⟨.refresh, _, .refresh origin, ?_⟩
      rw [refresh_eq e valid, encoded]
      exact compiledReadback_covers legal lower (upper.trans starts.le) valid.currLt
    · cases event with
      | ordinary =>
        obtain ⟨view, row, projected, made, found⟩ := emitted
        have atRow := (List.getElem?_eq_some_iff.mp found).2
        simp only [Fin.getElem_fin, atRow, MixedMemoryHistory.instruction, (compileInstructionEvent?_coordinates made).1] at operand
        obtain ⟨touch, used, rfl⟩ := List.mem_map.mp operand
        have actual := List.mem_of_getElem? found
        have memberTape : MemoryHistoryAccess.ofStamped before.clock touch ∈ MixedMemoryHistory.stream image source events rows :=
          List.mem_flatMap.mpr ⟨i, List.mem_finRange _, member⟩
        have projectedRow : row.routed ∈ rows.filterMap MixedCompiledRow.ordinaryObservation? := List.mem_filterMap.mpr ⟨_, actual, rfl⟩
        have bucket := EventBuckets.mem_ofChronological_iff.mpr ⟨_, projectedRow, RoutedEvent.forId?_self _ _⟩
        obtain ⟨ordered, seen, _, valid⟩ := releaseAdmissibleExecution_instructionBuckets run
        have eq : ordered = rows.filterMap MixedCompiledRow.ordinaryObservation? := Option.some.inj (seen.symm.trans (by simp [routeObservations?, routed]))
        subst ordered
        exact ⟨.ordinary row.routed.id, _, .ordinary projected made phase used (MixedMemoryHistory.canonical run.1 routed _ memberTape) bucket
          ((valid _).2 _ bucket), covered⟩
      | syscall call =>
        obtain ⟨s, n, found, step⟩ := run.1.1.2.step_at active
        cases Option.some.inj (path.symm.trans found)
        have clock : call.clock = before.clock := step.startsAt
        rw [Fin.getElem_fin, (List.getElem?_eq_some_iff.mp emitted).2, ← clock] at operand
        rw [← clock] at emitted phase covered
        exact ⟨.host .ecall, _, .ecall (List.mem_of_getElem? emitted) phase operand, covered⟩
  · obtain ⟨entry, used, rfl⟩ := List.mem_map.mp word
    have origin : entry ∈ HintReadTransfers.history image source events :=
      List.mem_flatMap.mpr ⟨⟨i.val, inside⟩, List.mem_finRange _, used⟩
    exact ⟨.host (.word entry.1), _, .hint origin, hint_origin run.1 atCut active used ▸ covered⟩

end SP1Clean.Export.WriteSourceRegistry
