import SP1Clean.Proofs.Completeness.MixedInstructionBuckets
import SP1Clean.Proofs.Completeness.MixedStateSchedule

/-! # Chronological normalization and register refresh inputs for a mixed local execution

There is one raw State push per tape cut. The ordinary or ECALL compiler supplies that push
and all register refreshes needed before its accesses. Physical StateBump rows arise only
when normalizing the raw push changes its limbs; MemoryBump rows retain their role order.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness.Target

/-- Bump inputs at one tape position, before any table bucketing or padding. -/
structure MixedBumpInput where
  /-- Unnormalized State message pushed by this ordinary instruction or ECALL. -/
  raw : StateRecord
  /-- Register refreshes in their physical access-role order before the instruction's touches. -/
  refreshes : List MemoryBumpEvent

namespace MixedBumpInput

/-- Both fields of an ordinary position come from its actual compiled row. -/
def ofOrdinary (row : CompiledInstructionEvent) : MixedBumpInput :=
  ⟨row.routed.rawPushState, row.memoryBumps⟩

/-- The ECALL adapter supplies one State push and its ordered C/B/A register refreshes. -/
def ofSyscall (frontier : AccessFrontier) (base : ℕ) (call : CoreSyscallEvent) : MixedBumpInput :=
  ⟨syscallPushedState call, (scheduleAccessPlan frontier base (syscallRegisterPlan call)).memoryBumps⟩

/-- Select a real state normalization exactly at a noncanonical push. -/
def stateBump? (input : MixedBumpInput) : Option StateBumpEvent :=
  if input.raw = input.raw.normalize then none else some input.raw.toBumpEvent

/-- The semantic selection uses exactly the three raw limb tests of the installed StateBump
demand guard, including cuts with a full upper limb. -/
theorem stateBump?_eq_none_iff (input : MixedBumpInput) : input.stateBump? = none ↔
    input.raw.clkLow < 2 ^ 24 ∧ input.raw.pc0 < 2 ^ 16 ∧ input.raw.pc1 < 2 ^ 16 := by
  have selected : input.stateBump? = none ↔ input.raw = input.raw.normalize := by
    unfold stateBump?
    split
    · rename_i canonical
      exact ⟨fun _ => canonical, fun _ => rfl⟩
    · rename_i changed
      constructor
      · intro impossible
        cases impossible
      · intro canonical
        exact (changed canonical).elim
  rw [selected]
  rcases input with ⟨⟨high, low, p0, p1, p2⟩, refreshes⟩
  change (StateRecord.mk high low p0 p1 p2) = (StateRecord.mk high low p0 p1 p2).normalize ↔
    low < 2 ^ 24 ∧ p0 < 2 ^ 16 ∧ p1 < 2 ^ 16
  constructor
  · intro equal
    have clock := congrArg StateRecord.clkHigh equal
    change high = high + (if 2 ^ 24 ≤ low then 1 else 0) at clock
    have first := congrArg StateRecord.pc0 equal
    change p0 = p0 - (if 2 ^ 16 ≤ p0 then 1 else 0) * 2 ^ 16 at first
    have last := congrArg StateRecord.pc2 equal
    change p2 = p2 + (if 2 ^ 16 ≤ p1 + (if 2 ^ 16 ≤ p0 then 1 else 0) then 1 else 0) at last
    have c : low < 2 ^ 24 := by
      by_contra! overflow
      rw [ite_eq_left overflow] at clock
      omega
    have a : p0 < 2 ^ 16 := by
      by_contra! overflow
      rw [ite_eq_left overflow] at first
      omega
    have b : p1 < 2 ^ 16 := by
      by_contra! overflow
      rw [ite_eq_right (Nat.not_le_of_lt a), Nat.add_zero, ite_eq_left overflow] at last
      omega
    exact ⟨c, a, b⟩
  · rintro ⟨clock, first, middle⟩
    let e := (StateRecord.mk high low p0 p1 p2).toBumpEvent
    have c : e.isClk = 0 := ite_eq_right (Nat.not_le_of_lt clock)
    have a : e.b0 = 0 := ite_eq_right (Nat.not_le_of_lt first)
    have b : e.b1 = 0 := by
      change (if 2 ^ 16 ≤ p1 + e.b0 then 1 else 0) = 0
      rw [a, Nat.add_zero, ite_eq_right (Nat.not_le_of_lt middle)]
    change StateRecord.mk high low p0 p1 p2 =
      ⟨high + e.isClk, low - e.isClk * 2 ^ 24, p0 - e.b0 * 2 ^ 16, p1 + e.b0 - e.b1 * 2 ^ 16, p2 + e.b1⟩
    rw [c, a, b]
    simp

/-- Chronological physical MemoryBump events, retaining register-role order within each cut. -/
def memoryRows (inputs : List MixedBumpInput) : List MemoryBumpEvent := inputs.flatMap (·.refreshes)

/-- Chronological physical StateBump events, including both ordinary instructions and ECALLs. -/
def stateRows (inputs : List MixedBumpInput) : List StateBumpEvent := inputs.filterMap stateBump?

/-- There is at most one selected StateBump row at a chronological position. -/
theorem stateRows_length_le (inputs : List MixedBumpInput) : (stateRows inputs).length ≤ inputs.length :=
  List.length_filterMap_le _ _

/-- Three register roles per tape position bound the complete refresh inventory. -/
theorem memoryRows_length_le (inputs : List MixedBumpInput)
    (roles : ∀ input ∈ inputs, input.refreshes.length ≤ 3) : (memoryRows inputs).length ≤ 3 * inputs.length := by
  induction inputs with
  | nil => simp [memoryRows]
  | cons head tail ih =>
    have front := roles head List.mem_cons_self
    have rest := ih (fun x member => roles x (List.mem_cons_of_mem _ member))
    change (head.refreshes ++ memoryRows tail).length ≤ _
    rw [List.length_append, List.length_cons]
    omega

private theorem split_at {inputs : List MixedBumpInput} {cut : ℕ} {input : MixedBumpInput}
    (present : inputs[cut]? = some input) : inputs.take cut ++ input :: inputs.drop (cut + 1) = inputs := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp present
  simpa only [List.take_succ_eq_append_getElem bound, same, List.append_assoc, List.singleton_append]
    using List.take_append_drop (cut + 1) inputs

/-- The physical MemoryBump index is the number of earlier refreshes plus the current
refresh's rank among the refreshes emitted at this cut. -/
theorem memoryRows_at {inputs : List MixedBumpInput} {cut role : ℕ} {input : MixedBumpInput}
    {bump : MemoryBumpEvent} (present : inputs[cut]? = some input) (selected : input.refreshes[role]? = some bump) :
    (memoryRows inputs)[(memoryRows (inputs.take cut)).length + role]? = some bump := by
  conv_lhs => arg 1; rw [← split_at present]
  simp only [memoryRows, List.flatMap_append, List.flatMap_cons]
  rw [List.getElem?_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1]
  exact selected

/-- If the raw State differs from its normalization, the selected StateBump occupies the
index immediately after all earlier selected cuts. -/
theorem stateRows_at {inputs : List MixedBumpInput} {cut : ℕ} {input : MixedBumpInput}
    {bump : StateBumpEvent} (present : inputs[cut]? = some input) (selected : input.stateBump? = some bump) :
    (stateRows inputs)[(stateRows (inputs.take cut)).length]? = some bump := by
  conv_lhs => arg 1; rw [← split_at present]
  simp only [stateRows, List.filterMap_append, List.filterMap_cons, selected, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

end MixedBumpInput

private theorem schedule_refresh_count (schedule : AccessSchedule) :
    schedule.memoryBumps.length ≤ schedule.stampedTouches.length := by
  simpa only [AccessSchedule.memoryBumps, AccessSchedule.stampedTouches, List.length_map] using
    List.length_filterMap_le ScheduledAccess.memoryBump? schedule.accesses

private theorem compiled_memoryBumps_length_le {view : SP1TransitionView} {frontier : AccessFrontier}
    {base : ℕ} {row : CompiledInstructionEvent} (made : compileInstructionEvent? view frontier base = some row) :
    row.memoryBumps.length ≤ row.plan.length := by
  have len := congrArg List.length (compileInstructionEvent?_stamped_touches made)
  simp only [List.length_map] at len
  exact (schedule_refresh_count row.schedule).trans len.le

/-- Collect both bump projections in one pass over the same compiler and timestamp frontier
used for ordinary routing. The index in the output is the original tape cut. -/
noncomputable def routeBumpInputs? (host : HostPolicy) (program : GuestProgram) :
    AccessFrontier → ExecutionState → List ExecutionEvent → Option (List MixedBumpInput)
  | _, _, [] => some []
  | frontier, current, event :: later =>
    emitMixedAccessStep? host program (current, frontier) event
      (fun next row => do
        let tail ← routeBumpInputs? host program row.nextFrontier next later
        return .ofOrdinary row :: tail)
      (fun next call => do
        let tail ← routeBumpInputs? host program (syscallFrontier frontier current.clock call) next later
        return .ofSyscall frontier current.clock call :: tail)

/-- Every collected position uses the frontier of its exact prefix and the row of its official
semantic successor. An ECALL retains its actual released register plan and raw state projection. -/
theorem routeBumpInputs?_at {host : HostPolicy} {program : GuestProgram} {frontier : AccessFrontier}
    {current : ExecutionState} {events : List ExecutionEvent} {inputs : List MixedBumpInput}
    (routed : routeBumpInputs? host program frontier current events = some inputs)
    {cut : ℕ} {event : ExecutionEvent} (present : events[cut]? = some event) :
    ∃ before incoming next,
      (events.take cut).foldlM (mixedAccessStep host program) (current, frontier) = some (before, incoming) ∧
      replayStep? host program before event = some next ∧
      match event with
      | .ordinary => ∃ view row, projectSP1Transition? program ⟨before.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
          compileInstructionEvent? view incoming before.clock = some row ∧ inputs[cut]? = some (.ofOrdinary row)
      | .syscall call => inputs[cut]? = some (.ofSyscall incoming before.clock call) := by
  induction events generalizing current frontier inputs cut with
  | nil => simp at present
  | cons head tail ih =>
    simp only [routeBumpInputs?, emitMixedAccessStep?, Option.bind_eq_bind, Option.bind_eq_some_iff] at routed
    obtain ⟨middle, step, built⟩ := routed
    cases head with
    | ordinary =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at built
      obtain ⟨view, seen, row, made, later, rest, rfl⟩ := built
      cases cut with
      | zero =>
        cases present
        exact ⟨current, frontier, middle, rfl, step, view, row, seen, made, rfl⟩
      | succ cut =>
        obtain ⟨s, f, next, reached, replay, atRow⟩ := ih rest present
        exact ⟨s, f, next, by simpa [mixedAccessStep, emitMixedAccessStep?, step, seen, made] using reached, replay,
          by cases event <;> exact atRow⟩
    | syscall call =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at built
      obtain ⟨later, rest, rfl⟩ := built
      cases cut with
      | zero =>
        cases present
        exact ⟨current, frontier, middle, rfl, step, rfl⟩
      | succ cut =>
        obtain ⟨s, f, next, reached, replay, atRow⟩ := ih rest present
        exact ⟨s, f, next, by simpa [mixedAccessStep, emitMixedAccessStep?, step] using reached, replay,
          by cases event <;> exact atRow⟩

private theorem routeBumps_from {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) {ordinary : List RoutedEvent}
    (observed : routeObservations? (policy p image) image.program AccessFrontier.initial source.realize events = some ordinary)
    {current last : ExecutionState} {later : List ExecutionEvent}
    (path : ExecutionPath (policy p image) image.program current later last)
    (before : List ExecutionEvent) (part : events = before ++ later) (frontier : AccessFrontier)
    (incoming : mixedAccessPrefix (policy p image) image.program source.realize events before.length = some (current, frontier)) :
    ∃ inputs, routeBumpInputs? (policy p image) image.program frontier current later = some inputs ∧
      inputs.length = later.length ∧ ∀ input ∈ inputs, input.refreshes.length ≤ 3 ∧
        input.raw.toBumpEvent.WellFormed ∧ ∀ row ∈ input.refreshes, row.WellFormed := by
  induction path generalizing before frontier with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | @cons current middle last event later step tail ih =>
    have present : events[before.length]? = some event := by simp [part]
    have part' : events = (before ++ [event]) ++ later := by simpa only [List.append_assoc, List.singleton_append] using part
    have after (outgoing : AccessFrontier) (ran : mixedAccessStep (policy p image) image.program (current, frontier) event = some (middle, outgoing)) :
        mixedAccessPrefix (policy p image) image.program source.realize events (before.length + 1) = some (middle, outgoing) := by
      simpa [mixedAccessPrefix_succ _ _ _ _ present, incoming] using ran
    cases event with
    | syscall call =>
      obtain ⟨s, f, next, _, same, _, _, _, _, _, _, _, valid⟩ := admissibleExecution_syscall_from_prefix execution present
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (incoming.symm.trans same))
      let entries := scheduleAccessPlan frontier current.clock (syscallRegisterPlan call)
      have len : entries.memoryBumps.length ≤ 3 :=
        (schedule_refresh_count entries).trans (le_of_eq (scheduleAccessPlan_stamped_length ..))
      have nextCut := after (syscallFrontier frontier current.clock call) (by simp [mixedAccessStep, emitMixedAccessStep?, step.replay])
      obtain ⟨inputs, routed, tailLen, good⟩ := ih _ part' _ (by simpa using nextCut)
      refine ⟨.ofSyscall frontier current.clock call :: inputs, ?_, by simp [tailLen], ?_⟩
      · simp [routeBumpInputs?, emitMixedAccessStep?, step.replay, routed]
      · intro input mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨len, (admissibleExecution_syscallPushedState execution present).1, valid⟩
        · exact good _ mem
    | ordinary =>
      obtain ⟨s, f, replay, same, bounded⟩ := admissibleExecution_mixedAccessPrefix execution before.length
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (incoming.symm.trans same))
      obtain ⟨s, next, view, row, replay', actual, seen, made, _, len, invariants⟩ :=
        admissibleExecution_compile_at execution present frontier
      obtain rfl := Option.some.inj (replay'.symm.trans replay)
      obtain rfl := Option.some.inj (actual.replay.symm.trans step.replay)
      have size := (compiled_memoryBumps_length_le made).trans len
      have nextCut := after row.nextFrontier (by simp [mixedAccessStep, emitMixedAccessStep?, step.replay, seen, made])
      obtain ⟨inputs, routed, tailLen, good⟩ := ih _ part' _ (by simpa using nextCut)
      obtain ⟨chosen, _, _, rank, _, _, raw, _⟩ := admissibleExecution_ordinaryPushedState execution observed present
      have position := compiled_mem_at_rank observed present incoming seen made nextCut
      obtain rfl := Option.some.inj (position.symm.trans rank)
      refine ⟨.ofOrdinary row :: inputs, ?_, by simp [tailLen], ?_⟩
      · simp [routeBumpInputs?, emitMixedAccessStep?, step.replay, seen, made, routed]
      · intro input mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨size, raw, (invariants bounded).2.1⟩
        · exact good _ mem

/-- Every mixed execution yields the exact two chronological inventories. Both consist solely
of valid normalization inputs and are bounded using the same semantic event count. -/
theorem admissibleExecution_mixedBumpInventory {limits : ResourceLimits} {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) :
    ∃ inputs, routeBumpInputs? (policy p image) image.program AccessFrontier.initial source.realize events = some inputs ∧
      inputs.length = events.length ∧ (MixedBumpInput.memoryRows inputs).length ≤ 3 * events.length ∧
      (MixedBumpInput.stateRows inputs).length ≤ events.length ∧
      (∀ bump ∈ MixedBumpInput.memoryRows inputs, bump.WellFormed) ∧
      ∀ bump ∈ MixedBumpInput.stateRows inputs, bump.WellFormed := by
  obtain ⟨ordinary, observed, _⟩ := admissibleExecution_routeObservations execution
  obtain ⟨inputs, routed, length, valid⟩ := routeBumps_from execution observed execution.1.2 [] rfl AccessFrontier.initial rfl
  refine ⟨inputs, routed, length, (MixedBumpInput.memoryRows_length_le inputs (fun input mem => (valid _ mem).1)).trans
    (by rw [length]), (MixedBumpInput.stateRows_length_le inputs).trans length.le, ?_, ?_⟩
  · intro bump member
    obtain ⟨input, mem, pos⟩ := List.mem_flatMap.mp member
    exact (valid input mem).2.2 bump pos
  · intro bump member
    obtain ⟨input, mem, found⟩ := List.mem_filterMap.mp member
    simp only [MixedBumpInput.stateBump?] at found
    split at found
    · contradiction
    · cases found
      exact (valid input mem).2.1

end SP1Clean.TraceGen
