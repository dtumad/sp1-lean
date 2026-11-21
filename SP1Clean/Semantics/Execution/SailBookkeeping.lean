module

public import SP1Clean.Semantics.Execution.ExecutionReplay
public import SP1Clean.Semantics.Sail.RetirementRegisters

/-! # Retirement observations of the existing Sail state

The ordinary instruction counter is distinct from the interaction clock and simulator cycle
counter. Its enable bit reads the official machine-mode filter and inhibit fields. Host calls
preserve these fields. The observation fold below only records retirement bookkeeping; it does
not execute instructions or define another machine state.
-/

@[expose] public section

namespace SP1Clean.Semantics

open LeanRV64D LeanRV64D.Functions Machine

/-- One observation update: only a normally retired ordinary instruction changes these slots. -/
def retirementTick (values : Bool × Option Bool × Option (BitVec 64)) (ordinary : Bool) :
    Bool × Option Bool × Option (BitVec 64) :=
  if ordinary then
    (values.1, some values.1, values.2.2.map (fun value => value + if values.1 then 1 else 0))
  else values

/-- The enable bit is constant; the architectural counter adds the number of ordinary steps,
with 64-bit wraparound. An empty ordinary inventory preserves even the original increment flag. -/
theorem retirementTick_fold {ρ : Type*} (ordinary : ρ → Bool) (rows : List ρ)
    (enabled : Bool) (flag : Option Bool) (counter : Option (BitVec 64)) :
    rows.foldl (fun values row => retirementTick values (ordinary row)) (enabled, flag, counter) =
      (enabled, if rows.countP ordinary = 0 then flag else some enabled,
        counter.map (fun value => value + BitVec.ofNat 64 (if enabled then rows.countP ordinary else 0))) := by
  induction rows generalizing flag counter with
  | nil => simp
  | cons row rest ih =>
    rw [List.foldl_cons]
    cases active : ordinary row with
    | false =>
      rw [show retirementTick (enabled, flag, counter) false = (enabled, flag, counter) from rfl, ih]
      simp [active]
    | true =>
      rw [show retirementTick (enabled, flag, counter) true =
        (enabled, some enabled, counter.map (fun value => value + if enabled then 1 else 0)) from rfl, ih]
      cases enabled <;> simp [active, Option.map_map, Function.comp_def, BitVec.ofNat_add,
        BitVec.add_comm]
      congr 1
      funext value
      rw [← BitVec.add_assoc, BitVec.add_comm _ value, BitVec.add_assoc]

/-- Walk backward over the host-only suffix. Its first host PC is the last ordinary successor;
with no ordinary event, preserve the source nextPC even at a terminal final PC. -/
private def nextPcReverse (initial finalPc : Option (BitVec 64)) : List ExecutionEvent → Option (BitVec 64)
  | [] => initial
  | .ordinary :: _ => finalPc
  | .syscall call :: rest => nextPcReverse initial (some call.pc) rest

/-- Final nextPC from semantic labels and endpoint PCs, without instruction-row data. -/
@[no_expose] def nextPcAfter (events : List ExecutionEvent) (initial finalPc : Option (BitVec 64)) : Option (BitVec 64) :=
  nextPcReverse initial finalPc events.reverse

@[simp] theorem nextPcAfter_nil (initial finalPc : Option (BitVec 64)) :
    nextPcAfter [] initial finalPc = initial := by
  simp only [nextPcAfter, List.reverse_nil, nextPcReverse]

@[simp] theorem nextPcAfter_ordinary (events : List ExecutionEvent) (initial finalPc : Option (BitVec 64)) :
    nextPcAfter (events ++ [.ordinary]) initial finalPc = finalPc := by
  simp only [nextPcAfter, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, nextPcReverse]

@[simp] theorem nextPcAfter_syscall (events : List ExecutionEvent) (call : CoreSyscallEvent)
    (initial finalPc : Option (BitVec 64)) :
    nextPcAfter (events ++ [.syscall call]) initial finalPc = nextPcAfter events initial (some call.pc) := by
  simp only [nextPcAfter, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, nextPcReverse]

/-- Without an ordinary event, the tape leaves nextPC at its initial value, whatever the endpoint
PC. -/
theorem nextPcAfter_of_countP_ordinary_eq_zero {events : List ExecutionEvent}
    (initial finalPc : Option (BitVec 64)) (noOrdinary : events.countP ExecutionEvent.isOrdinary = 0) :
    nextPcAfter events initial finalPc = initial := by
  induction events using List.reverseRecOn generalizing finalPc with
  | nil => exact nextPcAfter_nil initial finalPc
  | append_singleton events event ih =>
    rw [List.countP_append] at noOrdinary
    cases event with
    | ordinary => simp [ExecutionEvent.isOrdinary] at noOrdinary
    | syscall call =>
      rw [nextPcAfter_syscall]
      exact ih _ (by simpa [ExecutionEvent.isOrdinary] using noOrdinary)

/-- Local nextPC effects and the existing host-call PC authentication determine the whole tape's
bookkeeping. This does not require a separate physical trace or expose instruction splitting. -/
theorem replayEvents?_nextPC {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (success : replayEvents? policy program source events = some target)
    (effect : ∀ n current next event, events[n]? = some event →
      replayEvents? policy program source (events.take n) = some current →
      replayStep? policy program current event = some next →
        next.sail.regs.get? Register.nextPC =
          if event.isOrdinary then next.sail.regs.get? Register.PC else current.sail.regs.get? Register.nextPC) :
    target.sail.regs.get? Register.nextPC =
      nextPcAfter events (source.sail.regs.get? Register.nextPC) (target.sail.regs.get? Register.PC) := by
  induction events using List.reverseRecOn generalizing target with
  | nil => cases success; rfl
  | append_singleton events event ih =>
    rw [replayEvents?_append] at success
    obtain ⟨middle, prefixRan, last⟩ := Option.bind_eq_some_iff.mp success
    have step : replayStep? policy program middle event = some target := by
      simpa only [replayEvents?, Option.bind_fun_some] using last
    have finalEffect := effect events.length middle target event (by simp)
      (by simpa only [List.take_append_length] using prefixRan) step
    cases event with
    | ordinary => simpa only [nextPcAfter_ordinary, ExecutionEvent.isOrdinary_ordinary, ↓reduceIte] using finalEffect
    | syscall call =>
      have hostStep := (replayHost?_eq_some_iff _ _ _ _ _).mp step
      have pc : middle.sail.regs.get? Register.PC = some call.pc := by
        cases hostStep with
        | syscall ran =>
          obtain ⟨pc, execution, atPc, _, _, _, _, eventEq⟩ := HostState.step_observations ran
          rw [eventEq]
          exact atPc
      rw [nextPcAfter_syscall, ← pc, finalEffect]
      apply ih prefixRan
      intro n current next label atLabel replay step
      have bound := (List.getElem?_eq_some_iff.mp atLabel).1
      apply effect n current next label (by rwa [List.getElem?_append_left bound]) _ step
      simpa only [List.take_append_of_le_length (Nat.le_of_lt bound)] using replay

/-- The official retirement decision, optional increment flag and optional counter. -/
def retirementObservation (state : SailState) : Bool × Option Bool × Option (BitVec 64) :=
  (retirementEnabled state, state.regs.get? Register.minstret_increment, state.regs.get? Register.minstret)

/-- Every concrete host effect preserves the three retirement observations. -/
theorem HostExecution.retirement_observation (execution : HostExecution) (current : SailState) (pc : BitVec 64) :
    retirementObservation (execution.apply current pc) = retirementObservation current := by
  unfold retirementObservation retirementEnabled
  rw [execution.other_register_frame current pc Register.mcountinhibit (by decide) (by decide),
    execution.other_register_frame current pc Register.minstretcfg (by decide) (by decide),
    execution.other_register_frame current pc Register.minstret_increment (by decide) (by decide),
    execution.other_register_frame current pc Register.minstret (by decide) (by decide)]

/-- Observe the eventual refresh value and the two platform bookkeeping slots. -/
def platformObservation (state : SailState) :
    BitVec 64 × Option (BitVec 64) × Option (Option (Nat × LeanRV64D.event_csr)) :=
  (TryStepReduction.refreshedMip state, state.regs.get? Register.mip,
    state.regs.get? Register.written_event_index)

/-- One normal retirement refreshes pending interrupts and clears the event marker. -/
def platformTick
    (values : BitVec 64 × Option (BitVec 64) × Option (Option (Nat × LeanRV64D.event_csr))) (ordinary : Bool) :=
  if ordinary then (values.1, some values.1, some none) else values

/-- The platform fold distinguishes whether any ordinary instruction retired. -/
theorem platformTick_fold {ρ : Type*} (ordinary : ρ → Bool) (rows : List ρ)
    (pending : BitVec 64) (initial : Option (BitVec 64)) (marker : Option (Option (Nat × LeanRV64D.event_csr))) :
    rows.foldl (fun values row => platformTick values (ordinary row)) (pending, initial, marker) =
      (pending, if rows.countP ordinary = 0 then initial else some pending,
        if rows.countP ordinary = 0 then marker else some none) := by
  induction rows generalizing initial marker with
  | nil => rfl
  | cons row rest ih =>
    cases active : ordinary row
    · simpa [List.foldl_cons, platformTick, active] using ih initial marker
    · simpa [List.foldl_cons, platformTick, active] using ih (some pending) (some none)

/-- Every concrete host effect preserves interrupt registers and the event marker. -/
theorem HostExecution.platform_observation (execution : HostExecution) (current : SailState) (pc : BitVec 64) :
    platformObservation (execution.apply current pc) = platformObservation current := by
  unfold platformObservation TryStepReduction.refreshedMip
  rw [execution.other_register_frame current pc Register.misa (by decide) (by decide),
    execution.other_register_frame current pc Register.hvip (by decide) (by decide),
    execution.other_register_frame current pc Register.mip (by decide) (by decide),
    execution.other_register_frame current pc Register.written_event_index (by decide) (by decide)]

/-- A host-only suffix frames every Sail register other than PC and the x5 return slot. -/
theorem ExecutionPath.register_of_host_only {host : HostPolicy} {program : Soundness.Target.GuestProgram} {s t : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath host program s events t)
    (hostOnly : events.countP ExecutionEvent.isOrdinary = 0)
    (reg : Register) (notPc : reg ≠ .PC) (notX5 : reg ≠ .x5) :
    t.sail.regs.get? reg = s.sail.regs.get? reg := by
  induction path with
  | nil => rfl
  | @cons source middle last event later step _ ih =>
    cases step with
    | ordinary => simp [List.countP_cons] at hostOnly
    | syscall ran =>
      obtain ⟨pc, exec, _, _, _, _, targetEq, _⟩ := HostState.step_observations ran
      exact (ih (by simpa [List.countP_cons] using hostOnly)).trans
        (targetEq ▸ exec.other_register_frame source.sail pc reg notPc notX5)

end SP1Clean.Semantics
