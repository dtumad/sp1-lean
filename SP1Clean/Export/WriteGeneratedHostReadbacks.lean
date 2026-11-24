import SP1Clean.Export.WriteGeneratedHostSources
import SP1Clean.Proofs.Completeness.MixedMemoryRecords

/-! # Clock bounds of generated HINT_READ and refresh receipts

The positive receipts on the original HINT_READ and register refresh rows retain both
timestamps from the compiler. Disabled physical padding cannot contribute a unit receipt.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

/-- The original refresh receipt closes at its physical installation timestamp. -/
theorem refresh_eq (e : MemoryBumpEvent) (valid : e.WellFormed) :
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

/-- A genuine HINT_READ row publishes its actual prior word and two bounded timestamp pairs. -/
theorem hint_origin {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {i : ℕ} {before : ExecutionState} {f : AccessFrontier}
    (prefixAt : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events i = some (before, f))
    {event : ExecutionEvent} (atEvent : events[i]? = some event)
    {entry : Bool × HintReadWordChip.RowInput F} (used : entry ∈ (HintReadTransfers.rowsAt? image source events i).getD []) :
    let ram := entry.2.1.ram
    AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior = compiledReadback before.clock (MixedMemoryHistory.hint entry.2) ∧
      Counted.Bounded (AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior) := by
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
      have identified := hint_eq span pos (words j pos) found
      change _ = compiledReadback call.clock _ at identified
      rw [← clock] at identified
      refine ⟨identified, identified ▸ ?_⟩
      obtain ⟨current, frontier, path, actualPrefix, bounded⟩ := admissibleExecution_mixedAccessPrefix run i
      cases Option.some.inj (prefixAt.symm.trans actualPrefix)
      have finalTime := (run.1.2.clock_at atEvent path).trans_lt run.2.2.2.2.2.1
      change before.clock + 264 < 2 ^ 48 at finalTime
      have fits : before.clock < 2 ^ 48 := by omega
      apply Counted.bounded_compiled_entry _ before.clock _ fits
      obtain ⟨actual, _, _, _, _, stamp, _⟩ := words j pos
      cases Option.some.inj (actual.symm.trans found)
      change Semantics.MemoryMsg.timeNat _ < 2 ^ 48
      rw [stamp]
      exact (Nat.le_of_lt_succ (bounded _)).trans_lt fits
    · simp [HintReadTransfers.rowsAt?, atEvent, isRead] at used


/-- Every unit receipt in a compiled HINT_READ word table has two bounded split clocks, at
arbitrary evaluation data. The physical input gate excludes every disabled padding row. -/
theorem generated_hint_bounded {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (last : Bool) (data evaluation : ProverData F) (fit) {cells : Array F}
    (position : cells ∈ (HintReadTransfers.wordTable last (HintReadTransfers.history image source events) data fit).table)
    {receipt : Readback F} (paid : (1, receipt) ∈ rowRecords (.host (.word last)) (Environment.fromArray cells evaluation)) :
    Counted.Bounded receipt := by
  let entries := HintReadTransfers.history image source events
  let c := HintReadCoverage.component (p := SP1Prime) last
  let original := HintReadTransfers.wordTable last entries data fit
  change cells ∈ (HintReadTransfers.physicalInputs last entries).map (fun r => c.buildRow r original.data (.empty _)) at position
  obtain ⟨row, origin, rfl⟩ := List.mem_map.mp position
  let env := Environment.fromArray (c.buildRow row original.data (.empty _)) evaluation
  have decoded : valueFromOffset HintReadWordChip.RowInput 0 env = row := c.rowInput_buildRow row original.data evaluation (.empty _)
  change _ ∈ rowRecords _ env at paid
  rw [word_records, HintReadTransfers.row_activity, decoded,
    show HintReadCoverage.rowInput (last, env) = row.1 from congrArg Prod.fst decoded, List.mem_singleton] at paid
  obtain ⟨active, rfl⟩ := Prod.mk.inj paid
  rcases List.mem_append.mp origin with actual | padding
  · obtain ⟨entry, selected, rfl⟩ := List.mem_map.mp actual
    have occurs := (List.mem_filter.mp selected).1
    obtain ⟨i, _, used⟩ := List.mem_flatMap.mp occurs
    obtain ⟨before, f, _, prefixAt, _⟩ := admissibleExecution_mixedAccessPrefix run i.val
    exact (hint_origin run prefixAt (List.getElem?_eq_getElem i.isLt) used).2
  · obtain rfl := (List.mem_replicate.mp padding).2
    exact False.elim (one_ne_zero active)

/-- Every positive predecessor on the generated original register refresh table is bounded.
The active inputs use the matching event's two timestamps, and padding has zero weight. -/
theorem generated_refresh_bounded (registers : List MemoryBumpEvent) (states : List StateBumpEvent)
    (valid : ∀ e ∈ registers, e.WellFormed) (data evaluation : ProverData F) (mh sh) {cells : Array F}
    (position : cells ∈ (InstalledAssembly.bumpTables registers states data mh sh).1.table)
    {receipt : Readback F} (paid : (1, receipt) ∈ rowRecords .refresh (Environment.fromArray cells evaluation)) :
    Counted.Bounded receipt := by
  let original := (InstalledAssembly.bumpTables registers states data mh sh).1
  let c := providerTableFor (p := SP1Prime) .memoryBump
  rw [InstalledAssembly.bumpTables_registerRows] at position
  obtain ⟨row, origin, rfl⟩ := List.mem_map.mp position
  let env := Environment.fromArray (c.buildRow row original.data (.empty _)) evaluation
  have decoded : valueFromOffset MemoryBumpChip.Inputs 0 env = row := c.rowInput_buildRow row original.data evaluation (.empty _)
  change _ ∈ [((valueFromOffset MemoryBumpChip.Inputs 0 env).is_real, refreshReadback (valueFromOffset MemoryBumpChip.Inputs 0 env))] at paid
  rw [decoded, List.mem_singleton] at paid
  obtain ⟨active, rfl⟩ := Prod.mk.inj paid
  rcases List.mem_append.mp origin with actual | padding
  · obtain ⟨e, used, rfl⟩ := List.mem_map.mp actual
    have honest := valid e used
    change Counted.Bounded (InstalledAssembly.refreshEventReceipt e)
    rw [refresh_eq e honest]
    exact Counted.bounded_compiled_entry _ _ (honest.increases.trans honest.currLt) honest.currLt
  · obtain rfl := (List.mem_replicate.mp padding).2
    exact False.elim (one_ne_zero active)

end SP1Clean.Export.WriteSourceRegistry
