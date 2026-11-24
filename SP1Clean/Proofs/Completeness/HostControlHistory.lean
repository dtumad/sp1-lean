import SP1Clean.Proofs.Completeness.WritePacketHandoff
import SP1Clean.Native.Operations.HostExitBoundary

/-! # Terminal and no-effect host handoffs of the original mixed tape

Control calls need no independent host witness. Their fields are the instruction's clock,
raw code, inputs and result. The semantic path proves whether there was a terminal call,
including zero-valued exits and already-stopped empty segments.
-/

namespace SP1Clean.TraceGen.ControlHandlers

open Circuit Air.Flat Semantics Machine FormalModel.Shard Soundness.Target
private abbrev F := ZMod SP1Prime

/-- Select the original HALT table or the shared constrained ENTER/VERIFY table. -/
inductive Bucket where
  | halt | noop

/-- Filter by the released full syscall code. Both no-effect calls share one physical slot. -/
def Bucket.accepts : Bucket → BitVec 64 → Bool
  | .halt, code => decide (code = 0)
  | .noop, code => decide (code = SyscallKind.enterUnconstrained.code ∨ code = SyscallKind.verifyProof.code)

/-- Ordered CPU events in one of the two control tables. -/
def calls (kind : Bucket) (events : List ExecutionEvent) : List CoreSyscallEvent :=
  events.filterMap fun
    | .ordinary => none
    | .syscall call => if kind.accepts call.rawCode then some call else none

/-- These are the exact four words and both time limbs of the instruction receiver protocol. -/
def message (call : CoreSyscallEvent) : HostCallChip.Message F :=
  ⟨(call.clock / 2^24 : Nat), (call.clock % 2^24 : Nat), bitVecToWord call.rawCode,
    bitVecToWord call.arg1, bitVecToWord call.arg2, bitVecToWord call.result⟩

/-- Populated active HALT inputs in chronological order. -/
def haltRows (events : List ExecutionEvent) := (calls .halt events).map (fun c => HostHaltChip.populate (message c))

/-- Populated active ENTER and VERIFY rows in chronological order. -/
def noopRows (events : List ExecutionEvent) := (calls .noop events).map message

private theorem present {k : Bucket} {call : CoreSyscallEvent} {events : List ExecutionEvent} (member : call ∈ calls k events) :
    ExecutionEvent.syscall call ∈ events ∧ k.accepts call.rawCode = true := by
  obtain ⟨e, m, found⟩ := List.mem_filterMap.mp member
  cases e with
  | ordinary => contradiction
  | syscall c =>
    change (if k.accepts c.rawCode then some c else none) = some call at found
    split at found
    · cases Option.some.inj found
      exact ⟨m, by assumption⟩
    · contradiction

/-- Terminal calls in an arbitrary local execution are exactly its newly produced exit
status. In particular, a stopped identity has no real HALT, and a newly produced exit zero has one. -/
theorem halt_status {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath policy program source events target) :
    (calls .halt events).map (fun c => c.arg1.setWidth 32) =
      (if source.host.exitCode = none then target.host.exitCode else none).toList := by
  induction path with
  | nil base => cases base.host.exitCode <;> simp [calls]
  | @cons s mid t event es step rest ih =>
    rw [ite_eq_left step.running]
    have state := step.exit
    cases event with
    | ordinary => simpa [calls, state] using ih
    | syscall c =>
      by_cases halt : c.rawCode = 0
      · simp only [halt, ↓reduceIte] at state
        obtain ⟨rfl, rfl⟩ := rest.of_halted (by simp [state])
        simp [calls, Bucket.accepts, halt, state]
      · simp only [halt, ↓reduceIte] at state
        have skip : Bucket.halt.accepts c.rawCode = false := decide_eq_false halt
        have eq : calls .halt (.syscall c :: es) = calls .halt es := by
          simp only [calls, List.filterMap_cons, skip, Bool.false_eq_true, ↓reduceIte]
        rw [eq]
        simpa only [state, eq_self, ite_true] using ih

/-- On every genuine host cut the constructed handoff equals the active message of the
actual scheduled CPU instruction at its reconstructed predecessor frontier. -/
theorem instruction_at {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) {cut : Nat} {call : CoreSyscallEvent}
    (atCut : events[cut]? = some (.syscall call)) :
    ∃ before frontier,
      mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (before, frontier) ∧
      HostCallChip.message (syscallInstruction (p := SP1Prime) frontier call) = message call := by
  obtain ⟨current, frontier, _, _, built, step, _⟩ := admissibleExecution_syscall_from_prefix run atCut
  cases step with
  | syscall success =>
    obtain ⟨pc, exec, _, _, _, _, _, rfl⟩ := HostState.step_observations success
    exact ⟨_, _, built, syscallInstruction_hostMessage frontier current.clock pc exec⟩

/-- Successful execution alone establishes the active constraints of both registered handlers. -/
theorem honest {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) :
    (∀ r ∈ haltRows events, HostHaltChip.ProverAssumptions r) ∧ (∀ r ∈ noopRows events, HostNoopChip.ChoiceSpec r) := by
  have stepFor {k : Bucket} {call : CoreSyscallEvent} (m : call ∈ calls k events) :
      ∃ current next, ExecutionStep (policy SP1Prime image) image.program current (.syscall call) next := by
    obtain ⟨cut, bound, eq⟩ := List.getElem_of_mem (present m).1
    obtain ⟨current, _, next, _, _, step, _⟩ := admissibleExecution_syscall_from_prefix run ((List.getElem?_eq_getElem bound).trans (congrArg some eq))
    exact ⟨_, _, step⟩
  constructor
  · intro r inside
    obtain ⟨call, member, rfl⟩ := List.mem_map.mp inside
    have sel : call.rawCode = 0 := of_decide_eq_true (present member).2
    obtain ⟨current, _, step⟩ := stepFor member
    cases step with
    | syscall success =>
      obtain ⟨pc, exec, _, _, ran, _, _, rfl⟩ := HostState.step_observations success
      exact HostControl.halt_assumptions_of_run current.clock exec (SyscallKind.code_injective sel) current.host _ rfl _ ran
  · intro r inside
    obtain ⟨call, member, rfl⟩ := List.mem_map.mp inside
    have sel : call.rawCode = SyscallKind.enterUnconstrained.code ∨ call.rawCode = SyscallKind.verifyProof.code :=
      of_decide_eq_true (present member).2
    obtain ⟨current, _, step⟩ := stepFor member
    cases step with
    | syscall success =>
      obtain ⟨pc, exec, _, _, ran, _, _, rfl⟩ := HostState.step_observations success
      rcases sel with enter | verify
      · exact HostControl.choice_spec_of_run .enter current.clock exec (SyscallKind.code_injective enter) _ _ _ ran
      · exact HostControl.choice_spec_of_run .verify current.clock exec (SyscallKind.code_injective verify) _ _ _ ran

/-- Even an arbitrary bounded local segment cannot contain two HALT calls. -/
theorem halt_length {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) : (haltRows events).length ≤ 1 := by
  have sizes := congrArg List.length (halt_status run.1.2)
  simp only [List.length_map] at sizes
  rw [haltRows, List.length_map, sizes]
  cases ((if source.realize.host.exitCode = none then target.realize.host.exitCode else none) : Option (BitVec 32)) <;> simp

/-- The exact terminal word, without truncating any unverified high limbs. -/
theorem exit_words {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) :
    (haltRows events).map (fun r => r.call.arg1) =
      (if source.host.exitCode = none then target.host.exitCode else none).toList.map HostExitBoundary.encode := by
  have terminal := halt_status run.1.2
  change _ = (if source.host.exitCode = none then target.host.exitCode else none).toList at terminal
  rw [← terminal]
  simp only [haltRows, List.map_map]
  apply List.map_congr_left
  intro c member
  have spec := ((honest run).1 (HostHaltChip.populate (message c)) (List.mem_map_of_mem member)).1
  have small := (lt_min_iff.mp spec.2.2.2).2
  change Word.toNat (bitVecToWord (p := SP1Prime) c.arg1) < 2^32 at small
  rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord] at small
  change bitVecToWord c.arg1 = bitVecToWord ((c.arg1.setWidth 32).setWidth 64)
  apply congrArg bitVecToWord
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

end SP1Clean.TraceGen.ControlHandlers
