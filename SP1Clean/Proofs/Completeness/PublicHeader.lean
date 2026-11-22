import SP1Clean.FormalModel.ShardHeader
import SP1Clean.Native.Operations.LocalSourceBoundary
import SP1Clean.Native.Operations.ResourceBoundary
import SP1Clean.Native.Operations.SailBoundary
import SP1Clean.Native.Operations.CommitmentBoundary
import SP1Clean.Soundness.SP1Ensemble

/-! # Public verifier completeness on a semantic local execution -/

namespace SP1Clean.TraceGen
open Semantics Machine Circuit Soundness FormalModel.Shard

/-- The generated header satisfies the state verifier's prover assumptions and the literal
assertions of all four public boundary checkers in the supplied prover environment. -/
theorem statementExecution_headerChecks {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {limits : ResourceLimits} {commitments : CommitmentStatement} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : StatementExecution limits p commitments image source target events)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    let header := SP1StateBoundary.ofExecution (p := p) source target commitments
    sp1StateVerifierProverAssumptions header data hint ∧
      (LocalSourceBoundary.checker image source).Checks header data ∧
      (ResourceBoundary.checker limits source target).Checks header data ∧
      (SailBoundary.checker source target).Checks header data ∧
      (CommitmentBoundary.checker commitments).Checks header data := by
  let header := SP1StateBoundary.ofExecution (p := p) source target commitments
  obtain ⟨limbs, incoming, resources, sail, statement⟩ := execution.headerSpecs
  exact ⟨limbs, (LocalSourceBoundary.checks_iff image source header data).mpr incoming,
    (ResourceBoundary.checks_iff limits source target header data).mpr resources,
    (SailBoundary.checks_iff source target header data).mpr sail,
    (CommitmentBoundary.checker commitments).checks_of_proverAssumptions header data hint statement⟩

end SP1Clean.TraceGen
