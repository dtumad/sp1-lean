import SP1Clean.Proofs.Completeness.WritePacketHandoff
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Proofs.Operations.ClockOrderPopulate
import SP1Clean.Semantics.Host.BankReplay

/-! # Commitment-bank calls selected from the released execution

The two commitment banks use the original ECALL fields. Successful host dispatch supplies
the slot, result and 32-bit operand bounds, including the field bound for deferred commits.
-/

namespace SP1Clean.TraceGen.CommitBanks

open Circuit Air.Flat Machine Semantics Soundness.Target FormalModel.Shard HostCommitChip

private abbrev F := ZMod SP1Prime

/-- The canonical ECALL message before projecting a call into one of the sixteen bank lanes. -/
def message (call : CoreSyscallEvent) : HostCallChip.Message F :=
  HostCallChip.message (syscallInstruction AccessFrontier.initial call)

/-- The physical message agrees with the actual CPU row at every incoming AccessFrontier. -/
theorem message_eq (execution : HostExecution) (clock : ℕ) (pc : BitVec 64) (frontier : AccessFrontier) :
    message (execution.toEvent clock pc) = HostCallChip.message (syscallInstruction frontier (execution.toEvent clock pc)) := by
  unfold message
  rw [syscallInstruction_hostMessage, syscallInstruction_hostMessage]

private theorem slot_word (slot : Fin 8) : bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 slot.val) = slotWord slot := by
  fin_cases slot <;> rfl

private theorem call_of_run (deferred : Bool) (clock : ℕ) (pc : BitVec 64) (execution : HostExecution)
    (host : HostState) (image : ProgramImage) (context : HostReadContext)
    (success : host.run (policy SP1Prime image) context = some execution) (kind : execution.kind = bankKind deferred) :
    ∃ slot : Fin 8, slot.val = execution.arg1.toNat ∧ CallSpec deferred slot (message (execution.toEvent clock pc)) := by
  have result := ((host.run_eq_some_iff ..).mp success).2.2.2.2.1
  have stepped := ((host.run_eq_some_iff ..).mp success).2.2.2.2.2
  rw [kind] at stepped result
  have index : execution.arg1.toNat < 8 := by
    by_contra bad
    cases deferred <;> simp [bankKind, HostState.executeKind, bad] at stepped
  have value : execution.arg2.toNat < bound SP1Prime deferred := by
    cases deferred with
    | false =>
      change execution.arg2.toNat < 2 ^ 32
      simp [bankKind, HostState.executeKind, index] at stepped
      exact stepped.1
    | true =>
      change execution.arg2.toNat < min SP1Prime (2 ^ 32)
      rw [lt_min_iff]
      by_contra bad
      have absent : ¬ (execution.arg2.toNat < (policy SP1Prime image).characteristic ∧ execution.arg2.toNat < 2 ^ 32) := bad
      simp only [bankKind, ↓reduceIte, HostState.executeKind, dite_eq_left index, ite_eq_right absent, reduceCtorEq] at stepped
  let slot : Fin 8 := ⟨_, index⟩
  refine ⟨slot, rfl, ?_⟩
  unfold message
  rw [syscallInstruction_hostMessage]
  have code : bitVecToWord (p := SP1Prime) execution.kind.code = codeWord deferred := by
    rw [kind]; cases deferred <;> rfl
  have returns : bitVecToWord (p := SP1Prime) execution.result = codeWord deferred := by
    rw [result]; cases deferred <;> simp [bankKind, HostState.result, codeWord, bitVecToWord, SyscallKind.code]
  have reg : bitVecToWord (p := SP1Prime) execution.arg1 = slotWord slot := by
    simpa only [slot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using slot_word slot
  refine ⟨code, reg, returns, isU64_bitVecToWord _, ?_⟩
  change Word.toNat (bitVecToWord (p := SP1Prime) execution.arg2) < _
  rwa [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord]

/-- Every committed event supplies its genuine lane and native message at its original CPU clock. -/
theorem call_at {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events)
    {i : ℕ} {call : CoreSyscallEvent} (placed : events[i]? = some (.syscall call)) (deferred : Bool)
    (kind : call.rawCode = (bankKind deferred).code) :
    ∃ slot : Fin 8, slot.val = call.arg1.toNat ∧ CallSpec deferred slot (message call) ∧
      0 < call.clock ∧ call.clock < 2 ^ 48 ∧
      (message call).clk_high = (call.clock / 2 ^ 24 : ℕ) ∧ (message call).clk_low = (call.clock % 2 ^ 24 : ℕ) := by
  obtain ⟨s, f, next, _, _, step, _, _, phase, fit, _⟩ := admissibleExecution_syscall_from_prefix run placed
  cases step with
  | syscall dispatched =>
    obtain ⟨pc, execution, _, _, ran, _, _, rfl⟩ := HostState.step_observations dispatched
    have selected := SyscallKind.code_injective kind
    obtain ⟨slot, index, spec⟩ := call_of_run deferred s.clock pc execution s.host image _ ran selected
    change activeClockPhase s.clock at phase
    change s.clock % 8 = 1 at phase
    refine ⟨slot, index, spec, by change 0 < s.clock; omega, by change s.clock < 2^48; omega, ?_⟩
    unfold message
    rw [syscallInstruction_hostMessage]
    exact ⟨rfl, rfl⟩

/-- Select exactly one bank from the chronological execution tape, retaining its real CPU events. -/
def select (deferred : Bool) : ExecutionEvent → Option CoreSyscallEvent
  | .ordinary => none
  | .syscall call => if call.rawCode = (bankKind deferred).code then some call else none

/-- Bank calls in the original execution order. -/
def calls (deferred : Bool) (events : List ExecutionEvent) := events.filterMap (select deferred)

theorem select_iff (deferred : Bool) (event : ExecutionEvent) (call : CoreSyscallEvent) :
    select deferred event = some call ↔ event = .syscall call ∧ call.rawCode = (bankKind deferred).code := by
  cases event with
  | ordinary => simp [select]
  | syscall other => by_cases same : other.rawCode = (bankKind deferred).code <;> simp [select, same] <;> grind

/-- Successful host replay fixes the final values of each bank by the ordered selected argument pairs. -/
theorem call_arguments (deferred : Bool) (events : List ExecutionEvent) :
    (calls deferred events).map (fun c => (c.arg1,c.arg2)) = events.filterMap (bankEvent? deferred) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | ordinary => exact ih
    | syscall c =>
      by_cases same : c.rawCode = (bankKind deferred).code
      · simpa only [calls, List.filterMap_cons, select, bankEvent?, bankCall?, same, ↓reduceIte, List.map_cons] using
          congrArg ((c.arg1,c.arg2) :: ·) ih
      · simpa only [calls, List.filterMap_cons, select, bankEvent?, bankCall?, same, ↓reduceIte] using ih

private theorem call_clock {host : HostPolicy} {prog : GuestProgram} {s t : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep host prog s event t) {deferred : Bool} {c : CoreSyscallEvent} (selected : select deferred event = some c) :
    c.clock = s.clock := by
  obtain ⟨rfl, _⟩ := (select_iff deferred event c).mp selected
  cases step with
  | syscall step =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := HostState.step_observations step
    rfl

/-- Each bank's physical rows are strictly chronological, including when a slot is overwritten. -/
theorem ordered {host : HostPolicy} {prog : GuestProgram} {s t : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath host prog s events t) (deferred : Bool) :
    (∀ c ∈ calls deferred events, s.clock ≤ c.clock ∧ c.clock < t.clock) ∧
      (calls deferred events).Pairwise (fun a b => a.clock < b.clock) := by
  induction path with
  | nil => simp [calls]
  | @cons before middle after event rest step tail ih =>
    have advance := step.clock_lt
    have total := tail.clock
    cases selected : select deferred event with
    | none =>
      change (∀ c ∈ List.filterMap _ (event :: rest), _) ∧ List.Pairwise _ (List.filterMap _ (event :: rest))
      simp only [List.filterMap_cons, selected]
      exact ⟨fun c mem => ⟨advance.le.trans (ih.1 c mem).1, (ih.1 c mem).2⟩, ih.2⟩
    | some call =>
      have time := call_clock step selected
      change (∀ c ∈ List.filterMap _ (event :: rest), _) ∧ List.Pairwise _ (List.filterMap _ (event :: rest))
      simp only [List.filterMap_cons, selected, List.forall_mem_cons, List.pairwise_cons]
      exact ⟨⟨⟨by omega, by omega⟩, fun c mem => ⟨advance.le.trans (ih.1 c mem).1, (ih.1 c mem).2⟩⟩,
        fun c mem => time ▸ advance.trans_le (ih.1 c mem).1, ih.2⟩

/-- Every selected physical call has a valid slot and a strictly positive, representable timestamp. -/
theorem call_valid {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events)
    (deferred : Bool) {call : CoreSyscallEvent} (mem : call ∈ calls deferred events) :
    ∃ slot : Fin 8, slot.val = call.arg1.toNat ∧ CallSpec deferred slot (message call) ∧
      0 < call.clock ∧ call.clock < 2 ^ 48 ∧
      (message call).clk_high = (call.clock / 2 ^ 24 : ℕ) ∧ (message call).clk_low = (call.clock % 2 ^ 24 : ℕ) := by
  obtain ⟨event, listed, chosen⟩ := List.mem_filterMap.mp mem
  obtain ⟨rfl, kind⟩ := (select_iff deferred event call).mp chosen
  obtain ⟨i, located⟩ := List.mem_iff_getElem?.mp listed
  exact call_at run located deferred kind

end SP1Clean.TraceGen.CommitBanks
