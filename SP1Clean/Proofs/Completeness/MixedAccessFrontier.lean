import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Semantics.Host.HostFootprint

/-! # Constructing ordinary input timestamps across a mixed shard

Replay starts each local shard with the timestamp-zero snapshot providers. Ordinary rows reuse the
refresh-aware instruction compiler. Each ECALL posts x11, x10 and x5 at the three CPU offsets,
and a HINT_READ posts each padded output word at the host RAM offset. These are the Memory records
used by the installed row families. The separate WRITE observation circuit is outside this inventory.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

/-- Exact C/B/A register reads, read-backs and x5 write of the SyscallInstrs adapter. -/
def syscallRegisterPlan (event : CoreSyscallEvent) : InstructionAccessPlan :=
  [⟨.opC, .reg 11, event.arg2, event.arg2⟩,
   ⟨.opB, .reg 10, event.arg1, event.arg1⟩,
   ⟨.opA, .reg 5, event.rawCode, event.result⟩]

private theorem syscallRegisterPlan_wellFormed (event : CoreSyscallEvent) :
    (syscallRegisterPlan event).WellFormed := by
  constructor
  · simp [syscallRegisterPlan]
  · intro touch member
    simp only [syscallRegisterPlan, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · intro touch member reader
    simp only [syscallRegisterPlan, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · rfl
    · simp at reader

/-- The outgoing timestamps posted by the installed ECALL register and host RAM records. -/
def syscallFrontier (prior : AccessFrontier) (base : ℕ) (event : CoreSyscallEvent) : AccessFrontier
  | .reg index =>
    advancePlan prior base (syscallRegisterPlan event) (.reg index)
  | .ram cell =>
    if event.rawCode = SyscallKind.hintRead.code ∧
        event.arg1.toNat / 8 ≤ cell.toNat ∧
        cell.toNat < event.arg1.toNat / 8 + (event.arg2.toNat / 8 + 1)
    then base + AccessSlot.ram.recordOffset else prior (.ram cell)

/-- On a real HINT_READ, exactly the cells of the host's actual write receive the RAM timestamp,
including the extra word for empty and word-aligned hints. -/
theorem syscallFrontier_hintRead {host : HostState} {policy : HostPolicy} {context : HostReadContext}
    {execution : HostExecution} (ran : host.run policy context = some execution)
    (kind : execution.kind = .hintRead) (prior : AccessFrontier) (base : ℕ) (pc : BitVec 64) :
    ∃ write, execution.effect.write = some write ∧ ∀ cell : RamCell,
      syscallFrontier prior base (execution.toEvent base pc) (.ram cell) =
        if cell.toNat ∈ (MemorySpan.mk write.address write.bytes.length).cells
        then base + 1 else prior (.ram cell) := by
  have executed := ((host.run_eq_some_iff ..).mp ran).2.2.2.2.2
  rw [kind] at executed
  obtain ⟨bytes, rest, _, length, aligned, _, effect⟩ := (host.execute_hintRead_iff ..).mp executed
  refine ⟨⟨execution.arg1.toNat, hintWriteBytes bytes⟩, by rw [effect], ?_⟩
  intro cell
  simp only [syscallFrontier, HostExecution.toEvent, kind, true_and, AccessSlot.recordOffset_ram,
    MemorySpan.mem_cells, hintWriteBytes_length, length]
  congr 1
  apply propext
  omega

private theorem syscallFrontier_bounded (event : CoreSyscallEvent) {frontier : AccessFrontier}
    {base : ℕ} (bounded : frontier.BoundedAt base) :
    (syscallFrontier frontier base event).BoundedAt (base + syscallSchedule.duration) := by
  intro loc
  have before := bounded loc
  change _ < base + 264 + 1
  cases loc with
  | reg index =>
    have next := scheduleAccessPlan_outgoing_bounded_next (syscallRegisterPlan event) bounded (.reg index)
    rw [scheduleAccessPlan_outgoing] at next
    change advancePlan frontier base (syscallRegisterPlan event) (.reg index) < _
    change _ < base + 8 + 1 at next
    omega
  | ram cell =>
    simp only [syscallFrontier, AccessSlot.recordOffset_ram]
    split_ifs <;> omega

/-- One compiler pass threads the actual semantic state and the timestamps posted on Memory. -/
noncomputable def mixedAccessStep (policy : HostPolicy) (program : GuestProgram)
    (cursor : ExecutionState × AccessFrontier) (event : ExecutionEvent) :
    Option (ExecutionState × AccessFrontier) := do
  let next ← replayStep? policy program cursor.1 event
  match event with
  | .ordinary =>
    let view ← projectSP1Transition? program ⟨cursor.1.sail, ⟨.ordinary, next.sail⟩⟩
    let row ← compileInstructionEvent? view cursor.2 cursor.1.clock
    return (next, row.nextFrontier)
  | .syscall call => return (next, syscallFrontier cursor.2 cursor.1.clock call)

/-- The concrete frontier for a chronological prefix of a local statement. -/
noncomputable def mixedAccessPrefix (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) (cut : ℕ) :
    Option (ExecutionState × AccessFrontier) :=
  (events.take cut).foldlM (mixedAccessStep policy program) (source, AccessFrontier.initial)

/-- Extending the prefix consumes exactly the next chronological label. -/
theorem mixedAccessPrefix_succ (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) {cut : ℕ} {event : ExecutionEvent}
    (present : events[cut]? = some event) :
    mixedAccessPrefix policy program source events (cut + 1) =
      (mixedAccessPrefix policy program source events cut).bind fun cursor =>
        mixedAccessStep policy program cursor event := by
  have take : events.take (cut + 1) = events.take cut ++ [event] := by
    rw [List.take_succ_eq_append_getElem (List.getElem?_eq_some_iff.mp present).1,
      (List.getElem?_eq_some_iff.mp present).2]
  simp [mixedAccessPrefix, take, List.foldlM_append]

/-- Every semantic prefix yields a computed and bounded frontier, even when the incoming shard
clock is nonzero. Each intermediate semantic state is the one returned by the official replay. -/
theorem admissibleExecution_mixedAccessPrefix {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (cut : ℕ) :
    ∃ current frontier,
      executionTrajectory (policy p image) image.program source.realize events cut = some current ∧
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      frontier.BoundedAt current.clock := by
  induction cut with
  | zero =>
    exact ⟨source.realize, AccessFrontier.initial, rfl, rfl, fun _ => Nat.zero_lt_succ _⟩
  | succ cut ih =>
    obtain ⟨current, frontier, replay, built, bounded⟩ := ih
    cases present : events[cut]? with
    | none =>
      have ended := List.getElem?_eq_none_iff.mp present
      simpa [mixedAccessPrefix, executionTrajectory, List.take_of_length_le ended,
        List.take_of_length_le (Nat.le_succ_of_le ended)] using
        (show ∃ s f, executionTrajectory (policy p image) image.program source.realize events cut = some s ∧
          mixedAccessPrefix (policy p image) image.program source.realize events cut = some (s, f) ∧
          f.BoundedAt s.clock from ⟨current, frontier, replay, built, bounded⟩)
    | some event =>
      obtain ⟨now, next, replay', step⟩ := execution.1.2.step_at present
      have eq : now = current := Option.some.inj (replay'.symm.trans replay)
      subst now
      rw [executionTrajectory_succ _ _ _ _ present, replay, Option.bind_some, step.replay,
        mixedAccessPrefix_succ _ _ _ _ present, built, Option.bind_some]
      cases event with
      | ordinary =>
        obtain ⟨s, t, view, row, same, actual, projected, compiled, _, _, _⟩ :=
          admissibleExecution_compile_at execution present frontier
        have eq : s = current := Option.some.inj (same.symm.trans replay)
        subst s
        have eq' : t = next := Option.some.inj (actual.replay.symm.trans step.replay)
        subst t
        exact ⟨next, row.nextFrontier, rfl,
          by simp [mixedAccessStep, step.replay, projected, compiled],
          by rw [step.clock]; exact compileInstructionEvent?_frontier_bounded_next compiled bounded⟩
      | syscall call =>
        exact ⟨next, syscallFrontier frontier current.clock call, rfl,
          by simp [mixedAccessStep, step.replay],
          by rw [step.clock]; exact syscallFrontier_bounded call bounded⟩

/-- An actual syscall's incoming timestamps, including those consumed by HINT_READ, follow
from the same prefix as ordinary instructions. The canonical register scheduler supplies any
necessary high-window refreshes before the ECALL's three register records. -/
theorem admissibleExecution_syscall_from_prefix {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) :
    ∃ current frontier next,
      executionTrajectory (policy p image) image.program source.realize events cut = some current ∧
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      ExecutionStep (policy p image) image.program current (.syscall call) next ∧
      mixedAccessPrefix (policy p image) image.program source.realize events (cut + 1) =
        some (next, syscallFrontier frontier current.clock call) ∧
      frontier.BoundedAt current.clock ∧ activeClockPhase current.clock ∧ current.clock + 1 < 2 ^ 48 ∧
      let registers := scheduleAccessPlan frontier current.clock (syscallRegisterPlan call)
      (∀ index, registers.outgoing (.reg index) = syscallFrontier frontier current.clock call (.reg index)) ∧
      (∀ touch ∈ registers.stampedTouches, touch.previous < touch.current current.clock) ∧
      (∀ bump ∈ registers.memoryBumps, bump.WellFormed) := by
  obtain ⟨current, frontier, replay, built, bounded⟩ := admissibleExecution_mixedAccessPrefix execution cut
  obtain ⟨s, next, same, step⟩ := execution.1.2.step_at present
  have eq : s = current := Option.some.inj (same.symm.trans replay)
  subst s
  have phase := (execution.2.1 cut current _ present replay).1
  have total := execution.1.2.clock_at present replay
  change current.clock + 264 ≤ target.clock at total
  have final := execution.2.2.2.2.2.1
  have small : current.clock + 1 < 2 ^ 48 := by change target.clock < 2 ^ 48 at final; omega
  refine ⟨current, frontier, next, replay, built, step, ?_, bounded, phase, small, ?_,
    scheduleAccessPlan_previous_lt (syscallRegisterPlan_wellFormed call) bounded,
    scheduleAccessPlan_memoryBumps_wellFormed (syscallRegisterPlan_wellFormed call) bounded phase small⟩
  · rw [mixedAccessPrefix_succ _ _ _ _ present, built]
    simp [mixedAccessStep, step.replay]
  · intro index
    rw [scheduleAccessPlan_outgoing]
    rfl

/-- A mixed path supplies the predecessor timestamps for each ordinary row, and the row's exact
outgoing frontier becomes the next prefix. All twelve arithmetic families, including the x0 adapter, obtain their
existing table-specific validity predicates without an external frontier or timestamp premise. -/
theorem admissibleExecution_compile_from_prefix {limits : ResourceLimits} {p : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) :
    ∃ current frontier next view row,
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      projectSP1Transition? image.program ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      compileInstructionEvent? view frontier current.clock = some row ∧
      mixedAccessPrefix (policy p image) image.program source.realize events (cut + 1) =
        some (next, row.nextFrontier) ∧
      (∀ touch ∈ row.stamped, touch.previous < touch.current current.clock) ∧
      (∀ bump ∈ row.memoryBumps, bump.WellFormed) ∧
      (view.chipId ∈ [.add, .sub, .subw, .mul, .divRem, .aluX0, .addi, .addw, .bitwise, .lt,
          .shiftLeft, .shiftRight] →
        row.routed.id.Valid row.routed.event) := by
  obtain ⟨current, frontier, replay, built, bounded⟩ := admissibleExecution_mixedAccessPrefix execution cut
  obtain ⟨s, next, view, row, same, step, projected, compiled, _, _, invariants⟩ :=
    admissibleExecution_compile_at execution ordinary frontier
  have eq : s = current := Option.some.inj (same.symm.trans replay)
  subst s
  have phase := (execution.2.1 cut current .ordinary ordinary replay).1
  refine ⟨current, frontier, next, view, row, built, projected, compiled,
    by rw [mixedAccessPrefix_succ _ _ _ _ ordinary, built]; simp [mixedAccessStep, step.replay, projected, compiled],
    (invariants bounded).1, (invariants bounded).2.1,
    ?_⟩
  intro family
  change view.chipId ∈ [.add, .sub, .subw, .mul, .divRem] ++
    [.aluX0, .addi, .addw, .bitwise, .lt, .shiftLeft, .shiftRight] at family
  rcases List.mem_append.mp family with rtype | alu
  · exact compileInstructionEvent?_rtype_valid projected compiled rtype phase bounded
  · exact compileInstructionEvent?_alu_valid projected compiled alu phase bounded

end SP1Clean.TraceGen
