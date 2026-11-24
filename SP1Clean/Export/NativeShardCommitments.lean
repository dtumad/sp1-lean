import SP1Clean.Export.CommitmentReaderLedger

/-! # Commitment receipts on the public shard witness

The fixed source appends sixteen physical declaration sites. The two public assertion
verifiers inspect the same input and preserve every previously registered channel ledger.
-/

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Machine Semantics FormalModel.Shard

private abbrev F := ZMod SP1Prime
private abbrev declarationChannel := (CommitmentDeclaration.channel (p := SP1Prime)).toRaw

variable {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
  (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
  (w : EnsembleWitness (observer ctx)) (data : ProverData F)

/-- Install both public checks on the same physical rows, header and canonical data. -/
def withStatementChecks (base : EnsembleWitness (withDeclarations ctx)) : EnsembleWitness (assembly ctx) :=
  (ResourceBoundary.checker ctx.limits ctx.source ctx.target).lift
    (ens := (CommitmentBoundary.checker ctx.commitments).install (withDeclarations ctx))
    ((CommitmentBoundary.checker ctx.commitments).lift (ens := withDeclarations ctx) base)

private theorem lift_ledger {base : Ensemble F SP1PublicIO} (check : PublicVerifier F SP1PublicIO)
    (witness : EnsembleWitness base) (ch : RawChannel F) (member : ch ∈ base.channels) :
    (check.lift witness).interactionsWith ch = witness.interactionsWith ch :=
  (check.project_interactions (check.lift witness) ch (fun equal => check.channel_not_mem base (equal ▸ member))).symm

/-- The two public assertion channels leave the full physical ledger of any registered channel intact. -/
theorem withStatementChecks_ledger (base : EnsembleWitness (withDeclarations ctx)) (ch : RawChannel F)
    (member : ch ∈ (observer ctx).channels) :
    (withStatementChecks base).interactionsWith ch = base.interactionsWith ch := by
  have retained : ch ∈ (withDeclarations ctx).channels := member
  let commit := CommitmentBoundary.checker (p := SP1Prime) ctx.commitments
  let check := ResourceBoundary.checker (p := SP1Prime) ctx.limits ctx.source ctx.target
  have ready : ch ∈ (commit.install (withDeclarations ctx)).channels := List.mem_append_left _ retained
  exact (lift_ledger check (commit.lift base) ch ready).trans (lift_ledger commit base ch retained)

private theorem checked_header (base : EnsembleWitness (withDeclarations ctx)) :
    (withStatementChecks base).publicInput = base.publicInput := rfl

attribute [local irreducible] assembly withDeclarations withStatementChecks

/-- Canonically append the physical declaration source, then apply the statement and resource checks. -/
def statementWitness : EnsembleWitness (assembly ctx) :=
  withStatementChecks (ctx := ctx) (withFundedDeclarations execution w data)

theorem statementWitness_header : (statementWitness (ctx := ctx) execution w data).publicInput = w.publicInput :=
  (checked_header (ctx := ctx) (withFundedDeclarations execution w data)).trans
    (withFundedDeclarations_header execution w data)

theorem statementWitness_ledger (ch : RawChannel F) (member : ch ∈ (observer ctx).channels) :
    (statementWitness (ctx := ctx) execution w data).interactionsWith ch = w.interactionsWith ch ++
      (CommitmentReaders.provider execution.1.1 execution.2.2 data).interactionsWith ch :=
  (withStatementChecks_ledger (ctx := ctx) (withFundedDeclarations execution w data) ch member).trans
    (withFundedDeclarations_ledger execution w data ch)

/-- All prior channels except the declaration bus retain exactly their original traffic. -/
theorem statementWitness_other (ch : RawChannel F) (member : ch ∈ (observer ctx).channels)
    (different : ch ≠ declarationChannel) :
    (statementWitness (ctx := ctx) execution w data).interactionsWith ch = w.interactionsWith ch := by
  rw [statementWitness_ledger execution w data ch member]
  have silent : (CommitmentReaders.provider execution.1.1 execution.2.2 data).interactionsWith ch = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    change ch ∉ [declarationChannel]
    simpa only [List.mem_singleton] using different
  rw [silent, List.append_nil]

/-- A physical enumeration of the observer's declaration reads transports the funded bank result
to the complete witness, including both public checks and the sixteen-row declaration source. -/
theorem checked_of_bank_ledger (preset : ctx.limits.LE (.native SP1Prime))
    (origin : (w.interactionsWith declarationChannel).Perm
      (CommitmentReaders.reads execution.1.1 data false ++ CommitmentReaders.reads execution.1.1 data true)) :
    CheckedLedger ((statementWitness (ctx := ctx) execution w data).interactionsWith declarationChannel)
      (CommitmentReaders.sites execution.1.1) := by
  have same := origin.append_right ((CommitmentReaders.provider execution.1.1 execution.2.2 data).interactionsWith declarationChannel)
  have paid := CommitmentReaders.physical_checked execution.1.1 execution.2.2 data preset
  rw [statementWitness_ledger (ctx := ctx) execution w data declarationChannel (declarations_registered ctx)]
  exact paid.of_perm same

end SP1Clean.Export.NativeShard
