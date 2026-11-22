import SP1Clean.FormalModel.Contracts.ShardHeader
import SP1Clean.FormalModel.ShardResources
import SP1Clean.FormalModel.ShardRetirement

/-! # The complete execution supplies the public verifier's boundary facts -/

namespace SP1Clean.FormalModel.Shard
open Semantics Machine Soundness.Target OrdinaryObservation
open LeanRV64D (Register)

variable {p : ℕ} {limits : ResourceLimits} {image : ProgramImage}
  {source target : ExecutionSnapshot} {events : List ExecutionEvent}

private theorem enabled_realize (source : SailSnapshot) :
    retirementEnabled source.realize = retirementEnabled source.skeleton := by
  unfold retirementEnabled
  rfl

private theorem refresh_realize (source : SailSnapshot) :
    TryStepReduction.refreshedMip source.realize = TryStepReduction.refreshedMip source.skeleton := by
  unfold TryStepReduction.refreshedMip
  rfl

/-- The real count determines which executable retirement check accepts the supplied target. -/
theorem AdmissibleExecution.retirementModes
    (execution : AdmissibleExecution limits p image source target events) :
    ((events.countP ExecutionEvent.isOrdinary) = 0 → quiet source.sail target.sail = true) ∧
    ((events.countP ExecutionEvent.isOrdinary) ≠ 0 → refreshed source.sail target.sail = true) := by
  have dynamic := execution.1.dynamicMatch
  constructor
  · intro empty
    exact (quiet_iff _ _).mpr ⟨by rw [dynamic.increment, ite_eq_left empty],
      by rw [dynamic.interrupts, ite_eq_left empty], by rw [dynamic.eventIndex, ite_eq_left empty],
      dynamic.nextPC.trans (nextPcAfter_of_countP_ordinary_eq_zero _ _ empty)⟩
  · intro active
    exact (refreshed_iff _ _).mpr ⟨by rw [dynamic.increment, ite_eq_right active, enabled_realize],
      by rw [dynamic.interrupts, ite_eq_right active, refresh_realize], by rw [dynamic.eventIndex, ite_eq_right active],
      Executes.nextPC_bounded execution active⟩

/-- The executable comparison of invariant Sail fields holds on any complete local path. -/
theorem Executes.checkFrame (execution : Executes p image source target events) :
    source.sail.checkFrame target.sail = true := by
  have valid := execution.1
  have path := execution.2
  rw [image.program_eq valid.1.1] at path
  have frame := path.sailFrame valid.1.1 (fun _ selected => selected) valid.configured valid.romLoaded
  exact (SailSnapshot.checkFrame_iff ..).mpr ⟨fun reg => execution.frame.1.init reg,
    fun reg frozen => (frame.registers reg frozen).symm, frame.cycles.symm, frame.output.symm⟩

/-- Equal clocks force an empty tape. Otherwise the count of ordinary steps selects
the actual quiet or refreshed endpoint. This also covers host-only paths. -/
theorem AdmissibleExecution.checkStatic (execution : AdmissibleExecution limits p image source target events) :
    SailBoundary.checkStatic source target = true := by
  by_cases equal : source.clock = target.clock
  · have duration := execution.1.clock
    have count := event_count_le_ticks events
    have empty : events.length = 0 := by omega
    obtain rfl := List.length_eq_zero_iff.mp empty
    exact SailBoundary.checkStatic_of_realize_eq (ExecutionPath.nil_iff.mp execution.1.2).symm
      execution.1.1.2.1.init execution.1.1.2.2.1 execution.1.1.2.2.2
  · have modes := execution.retirementModes
    have checked : quiet source.sail target.sail = true ∨ refreshed source.sail target.sail = true := by
      by_cases zero : events.countP ExecutionEvent.isOrdinary = 0
      · exact Or.inl (modes.1 zero)
      · exact Or.inr (modes.2 zero)
    have bounds := execution.boundaryBounds
    simp only [SailBoundary.checkStatic, SailBoundary.checkRetirement, equal, ↓reduceIte,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨execution.1.checkFrame, bounds.2.2.2.2.1⟩, bounds.2.2.2.2.2⟩, checked⟩

/-- A new exit receipt comes from the final real HALT. The header contains the complete
argument value, including exits wider than one 16-bit limb. -/
theorem Executes.header_halt [Fact p.Prime] (execution : Executes p image source target events)
    {code : BitVec 32} (halted : SP1StateBoundary.haltCode source target = some code)
    (statement : CommitmentStatement) :
    ∃ leading call, events = leading ++ [.syscall call] ∧ call.rawCode = 0 ∧
      call.arg1.toNat = code.toNat ∧
      (SP1StateBoundary.ofExecution (p := p) source target statement).exit_code.val = call.arg1.toNat := by
  obtain ⟨running, stopped⟩ : source.host.exitCode = none ∧ target.host.exitCode = some code := by
    unfold SP1StateBoundary.haltCode at halted
    split at halted
    · exact ⟨by assumption, halted⟩
    · contradiction
  obtain ⟨leading, _, call, tape, _, step, zero, codeEq⟩ := execution.2.ends_in_halt running stopped
  have bounds := step.halt_bounds zero
  have arg : call.arg1.toNat = code.toNat := by
    rw [← codeEq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt bounds.2]
  refine ⟨leading, call, tape, zero, arg, ?_⟩
  change (((SP1StateBoundary.haltCode source target).getD 0).toNat : ZMod p).val = _
  rw [halted, Option.getD_some, ← arg]
  exact ZMod.val_natCast_of_lt bounds.1

/-- All public header contracts follow from the complete semantic statement. -/
theorem StatementExecution.headerSpecs [Fact p.Prime] {commitments : CommitmentStatement}
    (execution : StatementExecution limits p commitments image source target events) :
    let header := SP1StateBoundary.ofExecution (p := p) source target commitments
    header.LimbBounds ∧ LocalSourceBoundary.Spec image source header ∧
      ResourceBoundary.Spec limits source target header ∧ SailBoundary.Spec source target header ∧
      CommitmentBoundary.Spec commitments header := by
  obtain ⟨admitted, wellFormed, _⟩ := execution
  have incoming := SP1StateBoundary.ofExecution_source (p := p) source target commitments admitted.1.1.2.2.1
  have outgoing := SP1StateBoundary.ofExecution_target (p := p) source target commitments admitted.boundaryBounds.2.2.2.2.1
  refine ⟨SP1StateBoundary.ofExecution_limbBounds .., ⟨admitted.1.1, incoming, ?_⟩,
    ⟨admitted.boundaryBounds, outgoing.1⟩, ⟨admitted.checkStatic, outgoing, rfl⟩,
    SP1StateBoundary.ofExecution_commitment _ _ _ wellFormed⟩
  intro stopped
  obtain ⟨empty, _⟩ := admitted.1.of_halted stopped
  have clock := admitted.1.clock
  rw [empty] at clock
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at clock
  exact ⟨outgoing.1.1.trans ((congrArg (fun t : ℕ => ((t / 2 ^ 24 : ℕ) : ZMod p)) clock).trans incoming.1.symm),
    outgoing.1.2.trans ((congrArg (fun t : ℕ => ((t % 2 ^ 24 : ℕ) : ZMod p)) clock).trans incoming.2.1.symm)⟩

end SP1Clean.FormalModel.Shard
