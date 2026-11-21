import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.FormalModel.ShardResources
import SP1Clean.Semantics.Execution.ReleaseLinks

/-! # Execution language of the pinned SP1 release

An admitted Sail execution remains available through `AdmissibleExecution`. The released native
chips additionally require that each enabled JAL or JALR link write fits three limbs.
-/

namespace SP1Clean.FormalModel.Shard
open Semantics Machine

/-- The complete resource-bounded execution together with the released jump-link encoding. -/
noncomputable def ReleaseAdmissibleExecution (limits : ResourceLimits) (characteristic : ℕ)
    (image : ProgramImage) (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  AdmissibleExecution limits characteristic image source target events ∧
    ExecutionPath.ReleaseLinks (policy characteristic image) image.program source.realize events

/-- All original statement clauses and the link condition checked on the same event tape. -/
noncomputable def ReleaseStatementExecution (limits : ResourceLimits) (characteristic : ℕ)
    (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  ReleaseAdmissibleExecution limits characteristic image source target events ∧
    commitments.WellFormed characteristic ∧ commitments.Matches events

variable {limits : ResourceLimits} {characteristic : ℕ} {image : ProgramImage}
  {source left right target : ExecutionSnapshot} {events first second : List ExecutionEvent}

/-- The release adds only the active link-write limit to the broader commitment statement. -/
theorem releaseStatementExecution_iff (commitments : CommitmentStatement) :
    ReleaseStatementExecution limits characteristic commitments image source target events ↔
    StatementExecution limits characteristic commitments image source target events ∧
      ExecutionPath.ReleaseLinks (policy characteristic image) image.program source.realize events := by
  unfold ReleaseStatementExecution ReleaseAdmissibleExecution StatementExecution
  tauto

open LeanRV64D LeanRV64D.Functions in
/-- An ordinary occurrence supplies the actual source, fetched word and successful Sail decode
whose link the release checks. The caller supplies only the occurrence in its event tape. -/
theorem ReleaseAdmissibleExecution.link_at
    (execution : ReleaseAdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) :
    ∃ current pc word decoded,
      executionTrajectory (policy characteristic image) image.program source.realize events cut = some current ∧
      current.sail.regs.get? Register.PC = some pc ∧ image.program.fetchWord pc = some word ∧
      runSail (ext_decode word) current.sail = .ok decoded current.sail ∧ instructionLinkFits pc decoded := by
  obtain ⟨current, _, replay, _⟩ := execution.1.1.2.step_at ordinary
  have frame := execution.1.1.frame_prefix replay
  have encoded := execution.1.2.1 cut current .ordinary ordinary replay
  obtain ⟨pc, word, decoded, atPc, fetched, cfgDecode, _⟩ := encoded.2 rfl
  have ran := cfgDecode current.sail frame.1
  exact ⟨current, pc, word, decoded, replay, atPc, fetched, ran,
    execution.2 cut current ordinary replay pc word decoded atPc fetched ran⟩

/-- In particular empty and host-only tapes have exactly the original admissibility conditions. -/
theorem releaseAdmissibleExecution_iff_of_no_ordinary (none : .ordinary ∉ events) :
    ReleaseAdmissibleExecution limits characteristic image source target events ↔
      AdmissibleExecution limits characteristic image source target events :=
  ⟨And.left, fun execution => ⟨execution, ExecutionPath.releaseLinks_of_no_ordinary none⟩⟩

/-- Joining released segments reuses the broader resource and full-endpoint obligations. -/
theorem ReleaseAdmissibleExecution.append
    (firstPath : ReleaseAdmissibleExecution limits characteristic image source left first)
    (secondPath : ReleaseAdmissibleExecution limits characteristic image right target second)
    (same : left.equivalent right = true)
    (combined : ((executionResources (policy characteristic image) image.program source.realize first).combine
      (executionResources (policy characteristic image) image.program right.realize second)).Fits limits) :
    ReleaseAdmissibleExecution limits characteristic image source target (first ++ second) := by
  refine ⟨firstPath.1.append secondPath.1 same combined, (ExecutionPath.releaseLinks_append_iff firstPath.1.1.2).mpr ?_⟩
  rw [(ExecutionSnapshot.equivalent_iff _ _).mp same]
  exact ⟨firstPath.2, secondPath.2⟩

end SP1Clean.FormalModel.Shard
