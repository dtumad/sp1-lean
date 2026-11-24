import SP1Clean.Proofs.Completeness.MixedCompiledRows
import SP1Clean.Proofs.Completeness.HintReadTables
import SP1Clean.Proofs.Completeness.MemoryVersionHistory

/-! # Original Memory transfers in mixed execution order

Each CPU position contributes the compiler's existing refresh-aware access schedule. The same
position includes the actual inputs of its HINT_READ word tables, with their complete previous
and posted Memory messages. Repeated accesses and register aliases survive until the existing
per-location boundary construction selects the first and final records.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Semantics Machine FormalModel.Shard Soundness.Target

private abbrev F := ZMod SP1Prime

/-- Ordinary and ECALL transfers, expanded with the same MemoryBump entries as the physical compiler. -/
def cpu : MixedCompiledRow → List MemoryHistoryAccess
  | .ordinary row => MemoryHistoryAccess.ofAccessSchedule row.routed.clock row.schedule
  | .syscall frontier base call => MemoryHistoryAccess.ofAccessSchedule base (scheduleAccessPlan frontier base (syscallRegisterPlan call))

/-- A populated HINT_READ word transfers its raw prior and posted messages at the handler's clock. -/
def hint (input : HintReadWordChip.RowInput F) : MemoryHistoryAccess :=
  let ram := input.1.ram
  MemoryHistoryAccess.ofTouch ((ram.prior, clkNat ram.clk_high ram.clockLow), ram.pushed)

/-- The boundary compiler's chronological input. Both installed word variants are read from their
joint event order, before bucketing and padding. -/
noncomputable def stream (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (rows : List MixedCompiledRow) : List MemoryHistoryAccess :=
  (List.finRange rows.length).flatMap fun index => cpu rows[index] ++
    ((HintReadTransfers.rowsAt? image source events index.val).getD []).map (fun entry => hint entry.2)

private theorem mem_cpu {image : ProgramImage} {source : ExecutionSnapshot} {events : List ExecutionEvent}
    {rows : List MixedCompiledRow} {cut : ℕ} {row : MixedCompiledRow} (found : rows[cut]? = some row)
    {access : MemoryHistoryAccess} (member : access ∈ cpu row) : access ∈ stream image source events rows := by
  obtain ⟨inside, eq⟩ := List.getElem?_eq_some_iff.mp found
  refine List.mem_flatMap.mpr ⟨⟨cut, inside⟩, List.mem_finRange _, List.mem_append_left _ ?_⟩
  simpa only [Fin.getElem_fin, eq] using member

private theorem mem_hint {image : ProgramImage} {source : ExecutionSnapshot} {events : List ExecutionEvent}
    {rows : List MixedCompiledRow} {cut : ℕ} (inside : cut < rows.length)
    {entries : List (Bool × HintReadWordChip.RowInput F)} (found : HintReadTransfers.rowsAt? image source events cut = some entries)
    {entry : Bool × HintReadWordChip.RowInput F} (member : entry ∈ entries) : hint entry.2 ∈ stream image source events rows := by
  refine List.mem_flatMap.mpr ⟨⟨cut, inside⟩, List.mem_finRange _, List.mem_append_right _ ?_⟩
  simp only [found, Option.getD_some]
  exact List.mem_map_of_mem member

private theorem in_schedule {base : ℕ} {schedule : AccessSchedule} {loc : MemLoc}
    (member : loc ∈ schedule.stampedTouches.map (fun s => s.touch.loc)) :
    ∃ a ∈ MemoryHistoryAccess.ofAccessSchedule base schedule, a.loc = loc := by
  obtain ⟨stamped, occurs, rfl⟩ := List.mem_map.mp member
  obtain ⟨access, scheduled, rfl⟩ := List.mem_map.mp occurs
  exact ⟨_, List.mem_flatMap.mpr ⟨access, scheduled, List.mem_append_right _ List.mem_cons_self⟩, rfl⟩

private theorem outside_plan {image : ProgramImage} {source : ExecutionSnapshot} {events : List ExecutionEvent}
    {rows : List MixedCompiledRow} {cut : ℕ} {row : MixedCompiledRow} (found : rows[cut]? = some row)
    {loc : MemLoc} (fresh : loc ∉ touchedMemoryLocations (stream image source events rows))
    {plan : InstructionAccessPlan} {base : ℕ} {schedule : AccessSchedule}
    (origin : cpu row = MemoryHistoryAccess.ofAccessSchedule base schedule)
    (erased : schedule.stampedTouches.map StampedTouch.touch = plan) : loc ∉ plan.map PlannedTouch.loc := by
  intro member
  rw [← erased, List.map_map] at member
  obtain ⟨access, occurs, located⟩ := in_schedule (base := base) member
  exact fresh (mem_touchedMemoryLocations.mpr ⟨access, mem_cpu found (origin ▸ occurs), located⟩)

private theorem hint_location {cell : RamCell} {input : HintReadWordChip.RowInput F}
    (key : Address.toNat input.1.address = cell.toNat * 8) (lower : 2 ^ 16 ≤ cell.toNat * 8)
    (upper : cell.toNat * 8 < 2 ^ 48) : (hint input).loc = .ram cell := by
  let record := input.1.ram.prior
  have actual : record.addr0.val + record.addr1.val * 2 ^ 16 + record.addr2.val * 2 ^ 32 = cell.toNat * 8 := key
  have frame := MemoryBoundary.ram_location_of_key record _ lower upper (by omega) actual
  apply MemLoc.busAddress_injective_of_canonical (right := .ram cell) frame.1 ⟨by omega, upper⟩
  exact frame.2.1.symm.trans (by simpa only [MemLoc.busAddress, MemoryBoundary.address, Word.toNat, circuit_norm,
    ZMod.val_zero, zero_mul, add_zero] using actual)

private theorem hint_mem {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow} {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    (inside : cut < rows.length) (read : call.rawCode = SyscallKind.hintRead.code) {cell : RamCell}
    (lower : call.arg1.toNat / 8 ≤ cell.toNat) (upper : cell.toNat < call.arg1.toNat / 8 + (call.arg2.toNat / 8 + 1)) :
    MemLoc.ram cell ∈ touchedMemoryLocations (stream image source events rows) := by
  obtain ⟨current, _, frontier, cursor, _, bytes, _, _, reached, _, stored, _, node, _, _, _, length, _, span, _⟩ :=
    HintReadTransfers.of_admissibleExecution run present read
  let request : HintReadTransfers.Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
  have found : HintReadTransfers.rowsAt? image source events cut = some (request.rows frontier current.sail) := by
    simp [HintReadTransfers.rowsAt?, present, read, reached, stored, node, request]
  let j := cell.toNat - call.arg1.toNat / 8
  have pos : j < HintQueue.wordCount bytes := by unfold j HintQueue.wordCount; omega
  have aligned := span.2.1
  have address : call.arg1.toNat + j * 8 = cell.toNat * 8 := by unfold j; omega
  have output : (cell.toNat * 8, HintQueue.wordValue bytes j) ∈ HintQueue.wordWrites call.arg1.toNat bytes :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr pos, Prod.ext address rfl⟩
  rw [← request.writes frontier current.sail span] at output
  obtain ⟨entry, member, key⟩ := List.mem_map.mp output
  have auth := hint_location (Prod.mk.inj key).1 (by have := span.1; omega)
    (by have := span.2.2; unfold HintQueue.wordCount at pos; omega)
  exact mem_touchedMemoryLocations.mpr ⟨_, mem_hint inside found member, auth⟩

/-- A boundary location absent from the genuine mixed transfer stream still has timestamp zero at
every compiler cut. This includes all three ECALL registers, every padded HINT_READ word and every
ordinary operand, including aliases and registers which needed a refresh. -/
theorem zero_of_absent {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {loc : MemLoc} (fresh : loc ∉ touchedMemoryLocations (stream image source events rows))
    {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier)) :
    frontier loc = 0 := by
  induction cut generalizing current frontier with
  | zero => cases atCut; rfl
  | succ cut ih =>
    cases present : events[cut]? with
    | none =>
      have ended := List.getElem?_eq_none_iff.mp present
      apply ih (current := current)
      simpa only [mixedAccessPrefix, List.take_of_length_le ended, List.take_of_length_le (Nat.le_succ_of_le ended)] using atCut
    | some event =>
      obtain ⟨before, incoming, next, beforeCut, step, atRow⟩ := routeMixedRows?_at routed present
      change mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (before, incoming) at beforeCut
      have old := ih beforeCut
      rw [mixedAccessPrefix_succ _ _ _ _ present, beforeCut, Option.bind_some] at atCut
      cases event with
      | ordinary =>
        obtain ⟨view, row, projected, made, found⟩ := atRow
        have generated : mixedAccessStep (policy SP1Prime image) image.program (before, incoming) .ordinary = some (next, row.nextFrontier) := by
          simp [mixedAccessStep, emitMixedAccessStep?, step, projected, made]
        cases Option.some.inj (generated.symm.trans atCut)
        rw [compileInstructionEvent?_nextFrontier made, advancePlan_zero_iff]
        exact ⟨old, outside_plan found fresh rfl (compileInstructionEvent?_stamped_touches made)⟩
      | syscall call =>
        have generated : mixedAccessStep (policy SP1Prime image) image.program (before, incoming) (.syscall call) =
            some (next, syscallFrontier incoming before.clock call) := by simp [mixedAccessStep, emitMixedAccessStep?, step]
        cases Option.some.inj (generated.symm.trans atCut)
        cases loc with
        | reg index =>
          change advancePlan incoming before.clock (syscallRegisterPlan call) (.reg index) = 0
          rw [advancePlan_zero_iff]
          exact ⟨old, outside_plan atRow fresh rfl (scheduleAccessPlan_erase ..)⟩
        | ram cell =>
          change (if _ then _ else _) = 0
          split_ifs with touched
          · exact False.elim (fresh (hint_mem run present (List.getElem?_eq_some_iff.mp atRow).1 touched.1 touched.2.1 touched.2.2))
          · exact old

end SP1Clean.TraceGen.MixedMemoryHistory
