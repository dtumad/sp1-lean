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

private theorem issued_hint {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) (read : call.rawCode = SyscallKind.hintRead.code) :
    ∃ request : HintReadTransfers.Request, ∃ frontier sail,
      HintReadTransfers.rowsAt? image source events cut = some (request.rows frontier sail) ∧
      request.address = call.arg1.toNat ∧ request.bytes.length = call.arg2.toNat ∧ HintReadSpan.Domain request.address request.bytes.length := by
  obtain ⟨current, _, frontier, cursor, _, bytes, _, _, reached, _, stored, _, node, _, _, _, length, _, span, _⟩ :=
    HintReadTransfers.of_admissibleExecution run present read
  let request : HintReadTransfers.Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
  exact ⟨request, frontier, current.sail, by simp [HintReadTransfers.rowsAt?, present, read, reached, stored, node, request], rfl, length, span⟩

private theorem hint_mem {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow} {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    (inside : cut < rows.length) (read : call.rawCode = SyscallKind.hintRead.code) {cell : RamCell}
    (lower : call.arg1.toNat / 8 ≤ cell.toNat) (upper : cell.toNat < call.arg1.toNat / 8 + (call.arg2.toNat / 8 + 1)) :
    MemLoc.ram cell ∈ touchedMemoryLocations (stream image source events rows) := by
  obtain ⟨request, frontier, sail, found, addressEq, length, span⟩ := issued_hint run present read
  let j := cell.toNat - call.arg1.toNat / 8
  have pos : j < HintQueue.wordCount request.bytes := by unfold j HintQueue.wordCount; omega
  have aligned := span.2.1
  rw [addressEq] at aligned
  have address : call.arg1.toNat + j * 8 = cell.toNat * 8 := by unfold j; omega
  have output : (cell.toNat * 8, HintQueue.wordValue request.bytes j) ∈ HintQueue.wordWrites request.address request.bytes :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr pos, Prod.ext (addressEq ▸ address) rfl⟩
  rw [← request.writes frontier sail span] at output
  obtain ⟨entry, member, key⟩ := List.mem_map.mp output
  have auth := hint_location (Prod.mk.inj key).1 (by have := span.1; omega)
    (by have := span.2.2; unfold HintQueue.wordCount at pos; omega)
  exact mem_touchedMemoryLocations.mpr ⟨_, mem_hint inside found member, auth⟩

private theorem canonical_schedule {base : ℕ} {schedule : AccessSchedule}
    (honest : ∀ touch ∈ schedule.stampedTouches, touch.touch.loc.CanonicalAddress) :
    MemoryAddressesCanonical (MemoryHistoryAccess.ofAccessSchedule base schedule) := by
  intro record present
  obtain ⟨access, occurs, found⟩ := List.mem_flatMap.mp present
  rcases List.mem_append.mp found with bump | ordinary
  · obtain ⟨event, _, rfl⟩ := List.mem_map.mp bump
    trivial
  · cases List.mem_singleton.mp ordinary
    exact honest access.stamped (List.mem_map_of_mem occurs)

private theorem canonical_hint {request : HintReadTransfers.Request} {frontier : AccessFrontier} {sail : SailState}
    (span : HintReadSpan.Domain request.address request.bytes.length)
    {entry : Bool × HintReadWordChip.RowInput F} (present : entry ∈ request.rows frontier sail) : (hint entry.2).loc.CanonicalAddress := by
  have observed := List.mem_map_of_mem (f := fun pair : Bool × HintReadWordChip.RowInput F =>
    (Address.toNat pair.2.1.address, Word.toBitVec64 pair.2.1.ram.new_value)) present
  rw [request.writes frontier sail span] at observed
  obtain ⟨index, member, equal⟩ := List.mem_map.mp observed
  have key := (Prod.mk.inj equal).1.symm
  have bounds := span.2.2
  have aligned := span.2.1
  have lo := span.1
  have pos : index < request.bytes.length / 8 + 1 := List.mem_range.mp member
  let cell : RamCell := BitVec.ofNat 61 ((request.address + index * 8) / 8)
  have address : cell.toNat * 8 = request.address + index * 8 := by
    simp only [cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (request.address + index * 8) / 8 < 2 ^ 61)]
    omega
  have loc := hint_location (input := entry.2) (key.trans address.symm) (by omega) (by omega)
  rw [loc]
  change 32 ≤ cell.toNat * 8 ∧ cell.toNat * 8 < 2 ^ 48
  omega

/-- Every exposed original transfer has a canonical Memory address in the compiled mixed stream.
The enabled ordinary instruction's own guest-window bound covers RAM. The HINT_READ queue and
padded word domain authenticate every host word address. -/
theorem canonical {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows) :
    MemoryAddressesCanonical (stream image source events rows) := by
  obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
  intro access member
  obtain ⟨i, _, record⟩ := List.mem_flatMap.mp member
  have inside : i.val < events.length := i.isLt.trans_eq length
  have present := List.getElem?_eq_getElem inside
  generalize eventEq : events[i.val] = event at present
  obtain ⟨before, incoming, next, prefixAt, _, route⟩ := routeMixedRows?_at routed present
  change mixedAccessPrefix (policy SP1Prime image) image.program source.realize events i.val = some (before, incoming) at prefixAt
  obtain ⟨current, frontier, atCut, atCut', _⟩ := admissibleExecution_mixedAccessPrefix run i.val
  cases Option.some.inj (atCut'.symm.trans prefixAt)
  cases event with
  | ordinary =>
    obtain ⟨view, row, projected, made, found⟩ := route
    have atRow := (List.getElem?_eq_some_iff.mp found).2
    rw [show HintReadTransfers.rowsAt? image source events i.val = some [] by simp [HintReadTransfers.rowsAt?, present]] at record
    simp only [Fin.getElem_fin, atRow, Option.getD_some, List.map_nil, List.append_nil] at record
    apply canonical_schedule (schedule := row.schedule) _ access record
    intro touch occurs
    apply ((run.2.1 _ _ _ present atCut).2 rfl).canonical_locations (run.1.frame_prefix atCut).1 projected (compileInstructionEvent?_accessPlan made)
    rw [← compileInstructionEvent?_stamped_touches made]
    exact List.mem_map_of_mem (List.mem_map_of_mem occurs)
  | syscall call =>
    have atRow := (List.getElem?_eq_some_iff.mp route).2
    rcases List.mem_append.mp record with cpuAccess | word
    · simp only [Fin.getElem_fin, atRow] at cpuAccess
      apply canonical_schedule (schedule := scheduleAccessPlan incoming before.clock (syscallRegisterPlan call)) _ access cpuAccess
      intro touch occurs
      have planned := List.mem_map_of_mem (f := StampedTouch.touch) occurs
      rw [scheduleAccessPlan_erase] at planned
      simp only [syscallRegisterPlan, List.mem_cons, List.not_mem_nil, or_false] at planned
      rcases planned with eq | eq | eq <;> rw [eq] <;> trivial
    · obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp word
      by_cases read : call.rawCode = SyscallKind.hintRead.code
      · obtain ⟨request, _, _, found, _, _, span⟩ := issued_hint run present read
        rw [found, Option.getD_some] at listed
        exact canonical_hint span listed
      · simp [HintReadTransfers.rowsAt?, present, read] at listed

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
