import SP1Clean.Proofs.Completeness.MixedMemoryHistory
import SP1Clean.Proofs.Completeness.MemoryHistoryValues
import SP1Clean.Proofs.Completeness.UntouchedMemory

/-! # Sail values posted by the generated mixed Memory history

Ordinary instructions and ECALLs publish their canonical register schedules. Each padded
HINT_READ word also updates its aligned RAM cell at the host transfer's actual record clock.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Semantics Machine FormalModel.Shard Soundness.Target
open MemoryHistoryAccess

private abbrev F := ZMod SP1Prime

/-- Complete intermediate location image after ECALL register retirement and before its host RAM transfers. -/
def afterRegisters (source target : SailState) : LocationValues
  | .reg r => target.get_reg? r
  | .ram cell => locContent source (.ram cell)

/-- The ECALL operand roles consume their input registers and publish their authentic result register. -/
theorem syscall_register_values {p : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {call : CoreSyscallEvent} (step : ExecutionStep p program source (.syscall call) target) :
    (syscallRegisterPlan call).RunsFrom (locContent source.sail) (afterRegisters source.sail target.sail) := by
  obtain ⟨⟨_, code, arg1, arg2, _, result⟩, frame, _⟩ := step.syscall_sail_frame
  have c : locContent source.sail (.reg 11) = some call.arg2 := arg2
  have b : locContent source.sail (.reg 10) = some call.arg1 := arg1
  have a : locContent source.sail (.reg 5) = some call.rawCode := code
  simp only [syscallRegisterPlan, InstructionAccessPlan.runsFrom_cons_iff]
  refine ⟨c, ?_⟩
  rw [Function.update_eq_self_iff.mpr c.symm]
  refine ⟨b, ?_⟩
  rw [Function.update_eq_self_iff.mpr b.symm]
  refine ⟨a, InstructionAccessPlan.runsFrom_nil_iff.mpr ?_⟩
  funext loc
  cases loc with
  | reg i =>
    by_cases same : i = 5
    · subst i; rw [Function.update_self]; exact result
    · simpa only [afterRegisters, Function.update_of_ne (show MemLoc.reg i ≠ .reg 5 by simpa), locContent] using frame i same
  | ram => rfl

/-- The physical handler word consumes and posts the actual Sail word and frontier timestamp at its canonical destination cell. -/
theorem hint_word_endpoints {request : HintReadTransfers.Request} {index : ℕ} {frontier after : AccessFrontier}
    {source target : SailState} {store : HintQueue.Store} {entry : Bool × HintReadWordChip.RowInput F}
    (span : HintReadSpan.Domain request.address request.bytes.length) (pos : index < HintQueue.wordCount request.bytes)
    (atWord : request.WordAt index frontier after source target store)
    (found : (request.rows frontier source)[index]? = some entry) :
    let r := hint entry.2
    r.loc = .ram (request.cell index) ∧ r.loc.busAddress = request.destination index ∧
      r.previous = frontier r.loc ∧ r.current = after r.loc ∧
      locContent source r.loc = some r.pulled ∧ locContent target r.loc = some r.pushed ∧ r.current = request.clock + 1 := by
  obtain ⟨actual, _, _, prior, posted, priorTime, time, finish, _⟩ := atWord
  cases Option.some.inj (actual.symm.trans found)
  let dest := request.destination index
  have low : 2 ^ 16 ≤ dest := by
    have := span.1; dsimp [dest, HintReadTransfers.Request.destination]; omega
  have high : dest < 2 ^ 48 := by
    have := span.2.2; unfold HintQueue.wordCount at pos; dsimp [dest, HintReadTransfers.Request.destination]; omega
  have align : dest % 8 = 0 := by
    have := span.2.1; dsimp [dest, HintReadTransfers.Request.destination]; omega
  let cell := request.cell index
  have key : cell.toNat * 8 = dest := by
    change (BitVec.ofNat 61 ((BitVec.ofNat 64 dest).toNat / 8)).toNat * 8 = dest
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : dest < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : dest / 8 < 2 ^ 61)]
    omega
  have addr : cell.baseAddr = BitVec.ofNat 64 dest := by
    apply BitVec.eq_of_toNat_eq
    rw [Soundness.RamCell.baseAddr_toNat, key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have located := hint_location (input := request.wordRow index (frontier (.ram (request.cell index))) ((ramWord64? source (BitVec.ofNat 64 dest)).getD 0)) (cell := cell)
    ((Address.toNat_ofNat (p := SP1Prime) dest high).trans key.symm) (by omega) (by omega)
  refine ⟨located, ?_, ?_, ?_, ?_, ?_, time⟩
  · rw [located]; exact key
  · rw [located]; exact priorTime
  · rw [located]; exact time.trans finish.symm
  · rw [located]; change ramWord64? source cell.baseAddr = _; rwa [addr]
  · rw [located]; change ramWord64? target cell.baseAddr = _; rwa [addr]

private theorem hint_values_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    {before next : ExecutionState} {incoming : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (before, incoming))
    (nextCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (cut + 1) =
      some (next, syscallFrontier incoming before.clock call))
    {entry : Bool × HintReadWordChip.RowInput F} (listed : entry ∈ (HintReadTransfers.rowsAt? image source events cut).getD []) :
    (∃ cell, (hint entry.2).loc = .ram cell) ∧ locContent next.sail (hint entry.2).loc = some (hint entry.2).pushed ∧
      (hint entry.2).current = before.clock + 1 := by
  by_cases read : call.rawCode = SyscallKind.hintRead.code
  · obtain ⟨current, final, frontier, cursor, last, bytes, rest, tail, reached, doneAt, stored, _, node, _, _, _, _, clock, span, words⟩ :=
      HintReadTransfers.of_admissibleExecution run present read
    cases Option.some.inj (atCut.symm.trans reached)
    cases Option.some.inj (nextCut.symm.trans doneAt)
    let request : HintReadTransfers.Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
    have found : HintReadTransfers.rowsAt? image source events cut = some (request.rows incoming before.sail) := by
      simp [HintReadTransfers.rowsAt?, present, read, atCut, stored, node, request]
    rw [found, Option.getD_some] at listed
    obtain ⟨j, atJ⟩ := List.mem_iff_getElem?.mp listed
    have pos := (List.getElem?_eq_some_iff.mp atJ).1
    rw [request.rows_length] at pos
    rw [clock]
    obtain ⟨whereAt, _, _, _, _, pushed, stamped⟩ := hint_word_endpoints span pos (words j pos) atJ
    exact ⟨⟨_, whereAt⟩, pushed, stamped⟩
  · simp [HintReadTransfers.rowsAt?, present, read] at listed

/-- All original Memory transfers compiled at a single event, in their published event order. -/
noncomputable def batch (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (rows : List MixedCompiledRow) (index : Fin rows.length) : List MemoryHistoryAccess :=
  cpu rows[index] ++ ((HintReadTransfers.rowsAt? image source events index.val).getD []).map fun entry => hint entry.2

private theorem syscall_words_post {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    {before next : ExecutionState} {incoming : AccessFrontier}
    (step : ExecutionStep (policy SP1Prime image) image.program before (.syscall call) next)
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (before, incoming))
    (nextCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (cut + 1) =
      some (next, syscallFrontier incoming before.clock call)) :
    post (afterRegisters before.sail next.sail)
      (((HintReadTransfers.rowsAt? image source events cut).getD []).map fun entry => hint entry.2) = locContent next.sail := by
  apply post_eq_of_values
  · intro a occurs
    obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp occurs
    exact (hint_values_at run present atCut nextCut mem).2.1.symm
  · intro loc fresh
    cases loc with
    | reg => rfl
    | ram cell =>
      have outside : ¬(call.rawCode = SyscallKind.hintRead.code ∧ call.arg1.toNat / 8 ≤ cell.toNat ∧
          cell.toNat < call.arg1.toNat / 8 + (call.arg2.toNat / 8 + 1)) := by
        rintro ⟨read, lo, hi⟩
        obtain ⟨entry, mem, key⟩ := hint_at_cell run present read lo hi
        exact fresh _ (List.mem_map_of_mem mem) key
      exact (syscall_ram_frontier_zero step (fun _ => 0) cell (by simp [syscallFrontier, outside])).2.symm

/-- At each genuine event position, its original physical transfers produce the complete outgoing
Sail register/RAM image and lie strictly after the incoming CPU clock and before the next cut. -/
theorem batch_values {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (index : Fin rows.length) :
    ∃ before next, executionTrajectory (policy SP1Prime image) image.program source.realize events index.val = some before ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events (index.val + 1) = some next ∧
      post (locContent before.sail) (batch image source events rows index) = locContent next.sail ∧
      ∀ a ∈ batch image source events rows index, before.clock < a.current ∧ a.current ≤ next.clock := by
  obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
  have inside : index.val < events.length := index.isLt.trans_eq length
  have present := List.getElem?_eq_getElem inside
  generalize eventEq : events[index.val] = event at present
  obtain ⟨current, next, path, step⟩ := run.1.2.step_at present
  obtain ⟨before, incoming, after, atCut, replay, route⟩ := routeMixedRows?_at routed present
  change mixedAccessPrefix (policy SP1Prime image) image.program source.realize events index.val = some (before, incoming) at atCut
  obtain ⟨s, f, beforePath, found, _⟩ := admissibleExecution_mixedAccessPrefix run index.val
  cases Option.some.inj (atCut.symm.trans found)
  cases Option.some.inj (path.symm.trans beforePath)
  cases Option.some.inj (step.replay.symm.trans replay)
  refine ⟨current, next, path, ?_, ?_⟩
  · rw [executionTrajectory_succ _ _ _ _ present, path, Option.bind_some, step.replay]
  cases event with
  | ordinary =>
    obtain ⟨view, row, projected, made, emitted⟩ := route
    have noWords : HintReadTransfers.rowsAt? image source events index.val = some [] := by simp [HintReadTransfers.rowsAt?, present]
    simp only [batch, Fin.getElem_fin, (List.getElem?_eq_some_iff.mp emitted).2, noWords, Option.getD_some,
      List.map_nil, List.append_nil, cpu, (compileInstructionEvent?_coordinates made).1, compileInstructionEvent?_schedule made]
    have frame := run.1.frame_prefix path
    refine ⟨post_of_schedule (ordinary_plan_values step frame.1 frame.2.1 ((run.2.1 _ _ _ present path).2 rfl)
      projected (compileInstructionEvent?_accessPlan_generated projected made)) _ _, ?_⟩
    intro a occurs
    obtain ⟨lo, hi⟩ := current_in_window _ _ _ occurs
    exact ⟨lo, hi.trans (by rw [step.clock]; change _ ≤ current.clock + 8; omega)⟩
  | syscall call =>
    have nextCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events (index.val + 1) =
        some (next, syscallFrontier incoming current.clock call) := by
      rw [mixedAccessPrefix_succ _ _ _ _ present, atCut, Option.bind_some]
      simp [mixedAccessStep, emitMixedAccessStep?, step.replay]
    simp only [batch, Fin.getElem_fin, (List.getElem?_eq_some_iff.mp route).2, cpu, post_append,
      post_of_schedule (syscall_register_values step), syscall_words_post run present step atCut nextCut, true_and]
    intro a occurs
    have endClock : next.clock = current.clock + 264 := step.clock
    rcases List.mem_append.mp occurs with reg | word
    · obtain ⟨lo, hi⟩ := current_in_window _ _ _ reg
      exact ⟨lo, by omega⟩
    · obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp word
      rw [(hint_values_at run present atCut nextCut mem).2.2]
      omega

private theorem cut_clock_mono {p : HostPolicy} {program : GuestProgram} {source early late : ExecutionState}
    {events : List ExecutionEvent} {i j : ℕ} (ordered : i ≤ j)
    (before : executionTrajectory p program source events i = some early)
    (after : executionTrajectory p program source events j = some late) : early.clock ≤ late.clock := by
  have split := List.take_append_drop i (events.take j)
  rw [List.take_take, Nat.min_eq_left ordered] at split
  rw [replayEvents?_clock (events := events.take i) before, replayEvents?_clock (events := events.take j) after]
  conv_rhs => rw [← split, List.map_append, List.sum_append]
  omega

private theorem post_prefix {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {current : ExecutionState} (reached : executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current) :
    post (locContent source.realize.sail) (((List.finRange rows.length).take cut).flatMap (batch image source events rows)) = locContent current.sail := by
  induction cut generalizing current with
  | zero => cases reached; rfl
  | succ cut ih =>
    by_cases inRows : cut < rows.length
    · let i : Fin rows.length := ⟨cut, inRows⟩
      obtain ⟨before, next, atCut, atNext, values, _⟩ := batch_values run routed i
      cases Option.some.inj (reached.symm.trans atNext)
      rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using inRows),
        List.flatMap_append, List.flatMap_singleton, post_append, ih atCut]
      have same : (List.finRange rows.length)[cut]'(by simpa using inRows) = i := Fin.ext (by simp [i])
      rwa [same]
    · obtain ⟨actual, same, size⟩ := admissibleExecution_routeMixedRows run
      have length : rows.length = events.length := Option.some.inj (routed.symm.trans same) ▸ size
      have ended : events.length ≤ cut := by omega
      have past : (List.finRange rows.length).length ≤ cut := by simpa using Nat.le_of_not_gt inRows
      rw [List.take_of_length_le (Nat.le_succ_of_le past), ← List.take_of_length_le past]
      apply ih
      simpa only [executionTrajectory, List.take_of_length_le (Nat.le_succ_of_le ended), List.take_of_length_le ended] using reached

/-- The held word of the complete original mixed transfer stream is the actual Sail value at every
CPU cut and every canonical register or RAM location. The initial value comes from the realized
incoming boundary. Both touched and untouched locations use this same query. -/
theorem heldAt_cut {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (atCut : mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier))
    (loc : MemLoc) (canonicalLoc : loc.CanonicalAddress) :
    locContent current.sail loc = some (heldAt (source.sail.memorySnapshot.read loc) current.clock
      (memoryHistoryAt (stream image source events rows) loc)) := by
  obtain ⟨actual, f, path, found, _⟩ := admissibleExecution_mixedAccessPrefix run cut
  cases Option.some.inj (atCut.symm.trans found)
  let indices := List.finRange rows.length
  let emit := batch image source events rows
  have split : stream image source events rows = (indices.take cut).flatMap emit ++ (indices.drop cut).flatMap emit := by
    rw [← List.flatMap_append, List.take_append_drop]
    rfl
  have earlier : ∀ a ∈ (indices.take cut).flatMap emit, a.current ≤ current.clock := by
    intro a mem
    obtain ⟨idx, member, occurs⟩ := List.mem_flatMap.mp mem
    obtain ⟨j, bound, eq⟩ := List.mem_take_iff_getElem.mp member
    have coordinate : idx.val = j := by rw [← eq]; simp [indices]
    obtain ⟨before, next, _, after, _, window⟩ := batch_values run routed idx
    exact (window a occurs).2.trans (cut_clock_mono (by omega) after path)
  have later : ∀ a ∈ (indices.drop cut).flatMap emit, current.clock < a.current := by
    intro a mem
    obtain ⟨idx, member, occurs⟩ := List.mem_flatMap.mp mem
    obtain ⟨j, _, eq⟩ := List.mem_drop_iff_getElem.mp member
    have coordinate : idx.val = cut + j := by rw [← eq]; simp [indices]
    obtain ⟨before, next, prior, _, _, window⟩ := batch_values run routed idx
    exact (cut_clock_mono (by omega) path prior).trans_lt (window a occurs).1
  rw [split, heldAt_post earlier later (values := locContent source.realize.sail) loc _ (run.1.1.memory.locContent loc canonicalLoc)]
  exact congrFun (post_prefix run routed path).symm loc

end SP1Clean.TraceGen.MixedMemoryHistory
