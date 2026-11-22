import SP1Clean.Proofs.Completeness.MixedSyscallArms
import SP1Clean.Proofs.Completeness.MixedSyscallCoordinates
import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal
import SP1Clean.Proofs.Completeness.MixedCompiledRows

/-! # Constructing a complete syscall instruction row at every mixed execution cut

The same compiled row supplies the bundled native circuit's prover assumptions and decodes to
the executed architectural event. The incoming register frontier is determined by the prefix.
-/

namespace SP1Clean.TraceGen

open Circuit Machine Semantics Soundness.Target FormalModel.Shard

/-- The active instruction component for an actual ECALL, including WRITE. The receiver for
host effects is a separate component of the installed assembly. -/
theorem admissibleExecution_syscallInstruction {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (atCut : events[cut]? = some (.syscall call)) :
    ∃ current frontier,
      mixedAccessPrefix (policy SP1Prime image) image.program source.realize events cut = some (current, frontier) ∧
      let r := syscallInstruction (p := SP1Prime) frontier call
      r.is_real = 1 ∧ Soundness.syscallEventOfRow r = call ∧
        ∀ data hint, CoreSyscallChip.circuit.ProverAssumptions r data hint := by
  obtain ⟨current, frontier, next, before, atPrefix, step, _, _, phase, fit, _, ordered, _⟩ :=
    admissibleExecution_syscall_from_prefix execution atCut
  refine ⟨current, frontier, atPrefix, rfl, ?_⟩
  cases step with
  | syscall ran =>
    obtain ⟨pc, host, atPc, _, dispatched, _, _, rfl⟩ := HostState.step_observations ran
    let call := host.toEvent current.clock pc
    have law := host.rowLaw ((current.host.run_eq_some_iff ..).mp dispatched).2.2.2.2.1 current.clock pc
    have small : call.clock < 2 ^ 48 := Nat.lt_of_succ_lt fit
    have dest := Executes.pc_at execution before atPc
    refine ⟨syscallEventOfRow_syscallInstruction frontier call law.2.2.1 small dest, ?_⟩
    intro data hint
    obtain ⟨gates, sel, writeA, writeS, dispatchA, dispatchS, bA, bS, cA, cS, commitA, commitS, bytes⟩ :=
      syscallInstruction_arms_of_run dispatched current.clock pc frontier
    obtain ⟨cpu, a, b, c⟩ := syscallInstruction_readers (p := SP1Prime) frontier call phase ordered
    obtain ⟨pcA, pcS⟩ := syscallInstruction_pcArm (p := SP1Prime) frontier call
    refine ⟨?_, Or.inr rfl, fun _ => ?_⟩
    · exact ⟨gates, cpu, a, b, c, sel, writeA, writeS, pcA, pcS, dispatchA, dispatchS, bA, bS,
        cA, cS, commitA, commitS, syscallInstruction_pulledFacts frontier call, bytes⟩
    · change Word.isU64 (wordOfNat (p := SP1Prime) call.rawCode.toNat) ∧ _
      refine ⟨wordOfNat_isU64 _, host.kind, ?_⟩
      change host.kind.code = Word.toBitVec64 (wordOfNat (p := SP1Prime) host.kind.code.toNat)
      simp [toBitVec64_wordOfNat]

/-- Project the ECALL instruction rows from the same chronological compilation as ordinary
instructions and refresh rows. Each table input retains its own actual preceding timestamps. -/
def MixedCompiledRow.syscallInput? {p : ℕ} [Fact p.Prime] : MixedCompiledRow → Option (SyscallInstrsChip.Inputs (ZMod p))
  | .ordinary _ => none
  | .syscall incoming _ call => some (syscallInstruction incoming call)

private def CertifiedAt (e : ExecutionEvent) (entry : MixedCompiledRow) : Prop :=
  match e, entry with
  | .ordinary, .ordinary _ => True
  | .syscall call, .syscall frontier _ emitted =>
    let row := syscallInstruction (p := SP1Prime) frontier emitted
    row.is_real = 1 ∧ Soundness.syscallEventOfRow row = call ∧
      ∀ data hint, CoreSyscallChip.circuit.ProverAssumptions row data hint
  | _, _ => False

private theorem certifiedAt_filter {events : List ExecutionEvent} {compiled : List MixedCompiledRow}
    (same : List.Forall₂ CertifiedAt events compiled) :
    List.Forall₂ (fun call (r : SyscallInstrsChip.Inputs (ZMod SP1Prime)) =>
        r.is_real = 1 ∧ Soundness.syscallEventOfRow r = call ∧
        ∀ data hint, CoreSyscallChip.circuit.ProverAssumptions r data hint)
      (events.filterMap fun | .syscall call => some call | .ordinary => none)
      (compiled.filterMap MixedCompiledRow.syscallInput?) := by
  induction same with
  | nil => exact .nil
  | @cons e entry _ _ head _ tail =>
    cases e <;> cases entry
    · exact tail
    · exact head.elim
    · exact head.elim
    · exact .cons head tail

/-- All eight syscall kinds have a complete native instruction trace. The ordered relation
retains repeated identical calls and implies exact agreement on the length and every event. -/
theorem admissibleExecution_syscallInputs {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events) :
    ∃ compiled, routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events =
      some compiled ∧ List.Forall₂ (fun call (r : SyscallInstrsChip.Inputs (ZMod SP1Prime)) =>
        r.is_real = 1 ∧ Soundness.syscallEventOfRow r = call ∧
          ∀ data hint, CoreSyscallChip.circuit.ProverAssumptions r data hint)
        (events.filterMap fun | .syscall call => some call | .ordinary => none)
        (compiled.filterMap MixedCompiledRow.syscallInput?) := by
  obtain ⟨compiled, built, length⟩ := admissibleExecution_routeMixedRows execution
  refine ⟨compiled, built, certifiedAt_filter (List.forall₂_of_length_eq_of_get length.symm ?_)⟩
  intro cut e c
  have atCut := List.getElem?_eq_getElem e
  cases event : events[cut] with
  | ordinary =>
    rw [event] at atCut
    obtain ⟨_, _, _, _, _, emitted⟩ := routeMixedRows?_at built atCut
    obtain ⟨_, row, _, _, atRow⟩ := emitted
    have equal := (List.getElem?_eq_some_iff.mp atRow).2
    change CertifiedAt events[cut] compiled[cut]
    rw [event, equal]
    trivial
  | syscall call =>
    rw [event] at atCut
    obtain ⟨before, incoming, next, atPrefix, _, emitted⟩ := routeMixedRows?_at built atCut
    obtain ⟨current, frontier, reached, real, decoded, valid⟩ := admissibleExecution_syscallInstruction execution atCut
    change mixedAccessPrefix _ _ _ _ _ = _ at atPrefix
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atPrefix.symm.trans reached))
    have equal := (List.getElem?_eq_some_iff.mp emitted).2
    change CertifiedAt events[cut] compiled[cut]
    rw [event, equal]
    exact ⟨real, decoded, valid⟩

end SP1Clean.TraceGen
