import SP1Clean.Export.WriteObservationAssembly
import SP1Clean.Export.InstalledHintAssembly
import ToClean.Air.AppendedBuild
import SP1Clean.Proofs.Completeness.PublicHeader
import SP1Clean.FormalModel.ShardRelease

/-! # Public statement of the native eight-handler shard

The observation supervisor rebases the private queue at the public target. The appended fixed
table supplies the sixteen immutable commitment declarations. Its public encoding and the shard
resource bounds are checked by the existing verifier circuits on the resulting witness.
-/

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Semantics Machine Soundness FormalModel.Shard WriteObservationAssembly
private abbrev F := ZMod SP1Prime

variable (ctx : InstalledAssembly.Context)

/-- The WRITE observation assembly with the canonical public target token. -/
abbrev observer := native ctx.image ctx.source ctx.target

private theorem source_fresh :
    (CommitmentDeclaration.source (p := SP1Prime) ctx.commitments).circuit.name ∉ (observer ctx).tables.map (·.circuit.name) := by
  let final := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) ctx.target.host.io.hints
  change _ ∉ ((WriteSourceRegistry.withSources ctx.image ctx.source ctx.target final).tables ++ tables ctx.source ctx.target).map _
  rw [List.map_append,List.mem_append,WriteSourceRegistry.names_eq]
  exact not_or.mpr ⟨FixedHintAssembly.declarationFresh ctx.image ctx.source ctx.target final ctx.commitments,of_decide_eq_true rfl⟩

theorem declarations_registered : CommitmentDeclaration.channel.toRaw ∈ (observer ctx).channels := by
  let final := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) ctx.target.host.io.hints
  apply List.mem_append_left
  change _ ∈ channels ++ (WriteSourceRegistry.withSources ctx.image ctx.source ctx.target final).channels
  rw [WriteSourceRegistry.channels_eq]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ HostObserved.declarationsRegistered)

/-- Append the verifier-owned declaration source after the 117 original and observation tables. -/
def withDeclarations : Ensemble F SP1PublicIO :=
  CommitmentEnsemble.withSource ctx.commitments (observer ctx) (source_fresh ctx) (declarations_registered ctx)

/-- The native shard verifier for a program image, two complete boundaries, commitments and limits. -/
def assembly : Ensemble F SP1PublicIO :=
  ResourceEnsemble.install ctx.limits ctx.source ctx.target
    (CommitmentEnsemble.install ctx.commitments (observer ctx) (source_fresh ctx) (declarations_registered ctx))

/-- The 118th physical component is the immutable declaration source for precisely this statement. -/
theorem tables_eq : (assembly ctx).tables = (observer ctx).tables ++ [CommitmentDeclaration.source ctx.commitments] := rfl

theorem table_count : (assembly ctx).tables.length = 118 := by
  rw [tables_eq, List.length_append]
  change (preprocessing ctx.image ctx.source ctx.target (SP1Clean.HostHintQueueBoundary.initial ctx.target.host.io.hints)).tables.length + 1 = _
  rw [WriteObservationAssembly.table_count]

/-- Appending the immutable provider preserves every original row and the original verifier. -/
theorem declarationLayout : Ensemble.AppendedTables (observer ctx) (withDeclarations ctx)
    [CommitmentDeclaration.source ctx.commitments] := ⟨rfl, rfl⟩

/-- Rebind the observer and declaration rows to the same committed data store. -/
def appendDeclaration (w : EnsembleWitness (observer ctx)) (table : Table F)
    (component : table.component = CommitmentDeclaration.source ctx.commitments) :
    EnsembleWitness (withDeclarations ctx) :=
  (declarationLayout ctx).extend w [table] (by simp only [List.map_cons, List.map_nil, component])

theorem appendDeclaration_ledger (w : EnsembleWitness (observer ctx)) (table : Table F)
    (component : table.component = CommitmentDeclaration.source ctx.commitments) (ch : RawChannel F) :
    (appendDeclaration ctx w table component).interactionsWith ch = w.interactionsWith ch ++ table.interactionsWith ch := by
  unfold appendDeclaration
  rw [Ensemble.AppendedTables.extend_ledger]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Exactly the two public contracts added above the funded declaration table. -/
theorem statement_iff (header : SP1PublicIO F) (heights : List Nat) :
    (assembly ctx).Statement .logUp header heights ↔
      (withDeclarations ctx).Statement .logUp header heights ∧ CommitmentBoundary.Spec ctx.commitments header ∧
        ResourceBoundary.Spec ctx.limits ctx.source ctx.target header := by
  rw [assembly,ResourceEnsemble.statement_iff,CommitmentEnsemble.install]
  change (((CommitmentBoundary.checker ctx.commitments).install (withDeclarations ctx)).Statement .logUp header heights ∧ _) ↔ _
  rw [(CommitmentBoundary.checker ctx.commitments).statement_iff (withDeclarations ctx)
    (CommitmentBoundary.count_bound ctx.commitments) (CommitmentBoundary.Spec ctx.commitments) (fun input data =>
      ⟨CommitmentBoundary.spec_of_checks ctx.commitments,
       (CommitmentBoundary.checker ctx.commitments).checks_of_proverAssumptions input data (ProverHint.empty F)⟩)]
  exact and_assoc

/-- A release statement execution discharges both installed public checkers at its generated header
for every height vector. The remaining proposition checks the original declaration provider. -/
theorem statement_iff_of_execution {events : List ExecutionEvent}
    (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
    (heights : List Nat) :
    (assembly ctx).Statement .logUp ctx.header heights ↔ (withDeclarations ctx).Statement .logUp ctx.header heights := by
  obtain ⟨_,_,resources,_,commitments⟩ := ((releaseStatementExecution_iff ctx.commitments).mp execution).1.headerSpecs
  rw [statement_iff,and_iff_left ⟨commitments,resources⟩]

end SP1Clean.Export.NativeShard
