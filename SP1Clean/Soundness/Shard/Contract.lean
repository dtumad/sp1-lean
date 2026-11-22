import ToClean.Air.Realizes
import SP1Clean.FormalModel.Contracts.ShardHeader
import SP1Clean.FormalModel.ShardMachine
import SP1Clean.FormalModel.ShardRelease

/-! # End-to-end proof targets for the native shard

The shard contract is `Air.Flat.Realizes` at the SP1 machine: raw acceptance of an ensemble at
a public input is exactly an admissible trace of `sp1Machine` between fixed complete endpoints.
`SP1StateBoundary.ofExecution` computes the public header from those endpoints and the statement. Admissibility is the header identity, source
validity, the native resource profile, the released jump-link limit and the immutable commitment statement. `SoundnessTarget`
and `CompilerTarget` are the two fields of that realization: soundness starts at the raw Clean
statement, with no semantic conjunct added to the AIR, and the compiler must construct every
table and provider from data and prove success throughout the same semantic domain. Conflicting
declarations remain executable but are outside the proof statement. Digest-word coverage is not
assumed. An invalid image is rejected, because admissibility requires a valid source.

These target types describe the full eight-call resource-bounded artifact. Raw acceptance
of the installed seven-handler assembly already yields a trace between the two supplied complete
states with matching commitment declarations. Extending that proof to all eight calls and
the full resource profile, and constructing all tables from an admissible trace, remain open.
The public execution relation consists of the complete boundaries, tape, resources and
commitments. Released Rust comparison exercises the independent implementation.
-/

namespace SP1Clean.Soundness.Shard

open Air.Flat Semantics Machine FormalModel.Shard

variable {p : ℕ} [Fact p.Prime]

/-- Every public input names the same complete endpoints of one fixed shard. -/
def boundary (source target : ExecutionSnapshot) :
    SP1PublicIO (ZMod p) → ExecutionState × ExecutionState :=
  fun _ => (source.realize, target.realize)

/-- The header identity, source validity, resource profile, released jump links and commitments. -/
noncomputable def admissible (limits : ResourceLimits) (commitments : CommitmentStatement)
    (image : ProgramImage) (source target : ExecutionSnapshot) :
    SP1PublicIO (ZMod p) → List ExecutionEvent → Prop :=
  fun publicInput events =>
    publicInput = SP1StateBoundary.ofExecution source target commitments ∧ ExecutionSourceValid image source ∧
      nativeProfile limits p image source target events ∧
      ExecutionPath.ReleaseLinks (policy p image) image.program source.realize events ∧
      commitments.WellFormed p ∧ commitments.Matches events

/-- Raw AIR acceptance must yield an admissible machine trace to the complete outgoing state. -/
abbrev SoundnessTarget (ensemble : Ensemble (ZMod p) SP1PublicIO) (limits : ResourceLimits)
    (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) : Prop :=
  ensemble.Soundness Balance.logUp (fun _ _ => True) fun publicInput => ∃ events,
    Interpretation (sp1Machine p image) (boundary source target)
      (admissible limits commitments image source target) publicInput events

/-- Constructive completeness reuses Clean's generic compiler interface. Its domain contains
neither compiler success nor native row-readiness predicates. Executability is a further check. -/
abbrev CompilerTarget (ensemble : Ensemble (ZMod p) SP1PublicIO) (limits : ResourceLimits)
    (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) :=
  EnsembleCompiler ensemble Balance.logUp (List ExecutionEvent)
    (Interpretation (sp1Machine p image) (boundary source target)
      (admissible limits commitments image source target))

/-- An interpretation binds every public cell and the full release execution on the same tape. -/
theorem interpretation_iff {limits : ResourceLimits} {commitments : CommitmentStatement}
    {image : ProgramImage} {source target : ExecutionSnapshot} {header : SP1PublicIO (ZMod p)}
    {events : List ExecutionEvent} :
    Interpretation (sp1Machine p image) (boundary source target)
        (admissible limits commitments image source target) header events ↔
      header = SP1StateBoundary.ofExecution source target commitments ∧
        ReleaseStatementExecution limits p commitments image source target events := by
  simp only [Interpretation, boundary, admissible, ReleaseStatementExecution,
    ReleaseAdmissibleExecution, AdmissibleExecution, executes_iff (events := events)]
  tauto

/-- The intended single statement, conditional here on the two unfilled targets. -/
theorem statement_iff {ensemble : Ensemble (ZMod p) SP1PublicIO} {limits : ResourceLimits}
    {commitments : CommitmentStatement} {image : ProgramImage} {source target : ExecutionSnapshot}
    (sound : SoundnessTarget ensemble limits commitments image source target)
    (compiler : CompilerTarget ensemble limits commitments image source target) :
    (∃ heights, ensemble.Statement Balance.logUp (SP1StateBoundary.ofExecution source target commitments) heights) ↔
      ∃ events, ReleaseStatementExecution limits p commitments image source target events := by
  have realizes : Realizes (sp1Machine p image) ensemble Balance.logUp (boundary source target)
      (admissible limits commitments image source target) := ⟨sound, compiler⟩
  rw [realizes.statement_iff (SP1StateBoundary.ofExecution source target commitments)]
  refine exists_congr fun events => ?_
  simpa only [Interpretation, eq_self, true_and] using (interpretation_iff (p := p) (events := events)
    (source := source) (target := target) (image := image) (limits := limits) (commitments := commitments)
    (header := SP1StateBoundary.ofExecution source target commitments))

end SP1Clean.Soundness.Shard
