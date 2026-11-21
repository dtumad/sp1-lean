import ToClean.Air.Realizes
import SP1Clean.FormalModel.ShardMachine
import SP1Clean.FormalModel.ShardRelease

/-! # End-to-end proof targets for the native shard

The shard contract is `Air.Flat.Realizes` at the SP1 machine: raw acceptance of an ensemble at
a public input is exactly an admissible trace of `sp1Machine` between fixed complete endpoints.
`header` is their canonical public encoding. Admissibility is the header identity, source
validity, the native resource profile, the released jump-link limit and the immutable commitment statement. `SoundnessTarget`
and `CompilerTarget` are the two fields of that realization: soundness starts at the raw Clean
statement, with no semantic conjunct added to the AIR, and the compiler must construct every
table and provider from data and prove success throughout the same semantic domain. Conflicting
declarations remain executable but are outside the proof statement. Digest-word coverage is not
assumed. An invalid image is rejected, because admissibility requires a valid source.

These target types describe the full eight-call resource-bounded artifact. Raw acceptance
of the installed six-handler assembly already yields a trace between the two supplied complete
states with matching commitment declarations. Extending that proof to all eight calls and
the full resource profile, and constructing all tables from an admissible trace, remain open.
The public execution relation consists of the complete boundaries, tape, resources and
commitments. Released Rust comparison exercises the independent implementation.
-/

namespace SP1Clean.Soundness.Shard

open Air.Flat Semantics Machine FormalModel.Shard

variable {p : ℕ} [Fact p.Prime]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every public input names the same complete endpoints of one fixed shard. -/
def boundary (source target : ExecutionSnapshot) :
    PublicIO (ZMod p) → ExecutionState × ExecutionState :=
  fun _ => (source.realize, target.realize)

/-- The header identity, source validity, resource profile, released jump links and commitments. -/
noncomputable def admissible (limits : ResourceLimits) (commitments : CommitmentStatement)
    (image : ProgramImage) (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) :
    PublicIO (ZMod p) → List ExecutionEvent → Prop :=
  fun publicInput events =>
    publicInput = header ∧ ExecutionSourceValid image source ∧
      nativeProfile limits p image source target events ∧
      ExecutionPath.ReleaseLinks (policy p image) image.program source.realize events ∧
      commitments.WellFormed p ∧ commitments.Matches events

/-- Raw AIR acceptance must yield an admissible machine trace to the complete outgoing state. -/
abbrev SoundnessTarget (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
    (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) : Prop :=
  ensemble.Soundness Balance.logUp (fun _ _ => True) fun publicInput => ∃ events,
    Interpretation (sp1Machine p image) (boundary source target)
      (admissible limits commitments image source target header) publicInput events

/-- Constructive completeness reuses Clean's generic compiler interface. Its domain contains
neither compiler success nor native row-readiness predicates. Executability is a further check. -/
abbrev CompilerTarget (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
    (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) (header : PublicIO (ZMod p)) :=
  EnsembleCompiler ensemble Balance.logUp (List ExecutionEvent)
    (Interpretation (sp1Machine p image) (boundary source target)
      (admissible limits commitments image source target header))

/-- The intended single statement, conditional here on the two unfilled targets. -/
theorem statement_iff {ensemble : Ensemble (ZMod p) PublicIO} {limits : ResourceLimits}
    {commitments : CommitmentStatement} {image : ProgramImage} {source target : ExecutionSnapshot}
    {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble limits commitments image source target header)
    (compiler : CompilerTarget ensemble limits commitments image source target header) :
    (∃ heights, ensemble.Statement Balance.logUp header heights) ↔
      ∃ events, ReleaseStatementExecution limits p commitments image source target events := by
  have realizes : Realizes (sp1Machine p image) ensemble Balance.logUp (boundary source target)
      (admissible limits commitments image source target header) := ⟨sound, compiler⟩
  rw [realizes.statement_iff header]
  refine exists_congr fun events => ?_
  -- `executes_iff` is instantiated by hand: `events : List (sp1Machine …).Event` only unfolds to
  -- `List ExecutionEvent` at default transparency, which `simp` no longer does when assigning it.
  simp only [boundary, admissible, ReleaseStatementExecution, ReleaseAdmissibleExecution, AdmissibleExecution, true_and,
    executes_iff (events := events)]
  tauto

end SP1Clean.Soundness.Shard
