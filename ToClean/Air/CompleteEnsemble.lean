module

public import Clean.Air.FlatEnsemble

/-! # Sound and complete flat ensembles

## Gap against upstream

Clean defines both `Ensemble.Soundness` and `Ensemble.Completeness`, but its `FormalEnsemble`
bundles only soundness. `CompleteEnsemble` adds the missing direction without modifying that
interface. `EnsembleCompiler` additionally records a proof-independent partial witness constructor:
it rejects invalid candidate executions and succeeds on every execution in the semantic relation.

The specification remains a relation on semantic executions, independent of the circuit witness.
In particular, compiler success is a conclusion of completeness, never its domain definition.
These interfaces do not claim that an arbitrary Lean compiler can be exported to another language.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The complete raw AIR obligation for one witness at a specified public input. -/
def EnsembleWitness.Valid {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (balance : Balance F) (publicInput : PublicIO F) : Prop :=
  ens.interactionsFit balance witness.heights ∧
    witness.publicInput = publicInput ∧ witness.Constraints ∧ witness.Balanced balance

/-- A valid witness proves exactly Clean's raw ensemble statement. -/
theorem EnsembleWitness.Valid.statement {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} {balance : Balance F} {publicInput : PublicIO F}
    (valid : witness.Valid balance publicInput) : ens.Statement balance publicInput witness.heights :=
  ⟨valid.1, witness, valid.2.1, rfl, valid.2.2⟩

/-- A formal ensemble with both directions of its semantic contract. -/
structure CompleteEnsemble (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] (balance : Balance F)
    extends FormalEnsemble F PublicIO balance where
  completeness : ensemble.Completeness balance Assumptions Spec

/-- The public statement of a complete ensemble is its semantic specification. -/
theorem CompleteEnsemble.statement_iff {balance : Balance F}
    (c : CompleteEnsemble F PublicIO balance) (publicInput : PublicIO F) :
    (∃ heights, c.Assumptions publicInput heights ∧
      c.ensemble.Statement balance publicInput heights) ↔ c.Spec publicInput := by
  constructor
  · rintro ⟨heights, assumptions, statement⟩
    exact c.soundness publicInput heights assumptions statement
  · exact c.completeness publicInput

/-- A witness compiler for an independently defined execution relation.

`compile` consumes data, not a proof of validity. Soundness checks both the supplied execution and
the resulting AIR witness; completeness establishes success for every valid execution. The field
contains a Lean function, so executable implementations must separately avoid noncomputable code.
-/
structure EnsembleCompiler (ens : Ensemble F PublicIO) (balance : Balance F) (Execution : Type)
    (Executes : PublicIO F → Execution → Prop) where
  compile : PublicIO F → Execution → Option (EnsembleWitness ens)
  sound : ∀ publicInput execution witness, compile publicInput execution = some witness →
    Executes publicInput execution ∧ witness.Valid balance publicInput
  complete : ∀ publicInput execution, Executes publicInput execution →
    ∃ witness, compile publicInput execution = some witness

/-- Successful compilation characterizes the semantic domain, independently of any choice of
proof of execution validity. -/
theorem EnsembleCompiler.succeeds_iff {ens : Ensemble F PublicIO} {balance : Balance F} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens balance Execution Executes)
    (publicInput : PublicIO F) (execution : Execution) :
    (∃ witness, c.compile publicInput execution = some witness) ↔ Executes publicInput execution := by
  constructor
  · rintro ⟨witness, compiled⟩
    exact (c.sound publicInput execution witness compiled).1
  · exact c.complete publicInput execution

/-- Constructive witness compilation supplies the existential direction of AIR correctness. -/
theorem EnsembleCompiler.completeness {ens : Ensemble F PublicIO} {balance : Balance F} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens balance Execution Executes) :
    ens.Completeness balance (fun _ _ => True) (fun publicInput => ∃ execution, Executes publicInput execution) := by
  rintro publicInput ⟨execution, valid⟩
  obtain ⟨witness, compiled⟩ := c.complete publicInput execution valid
  exact ⟨witness.heights, trivial, (c.sound publicInput execution witness compiled).2.statement⟩

/-- Combine a proved raw-AIR soundness theorem with a complete witness compiler. -/
def EnsembleCompiler.toCompleteEnsemble {ens : Ensemble F PublicIO} {balance : Balance F} {Execution : Type}
    {Executes : PublicIO F → Execution → Prop} (c : EnsembleCompiler ens balance Execution Executes)
    (soundness : ens.Soundness balance (fun _ _ => True)
      (fun publicInput => ∃ execution, Executes publicInput execution)) :
    CompleteEnsemble F PublicIO balance where
  ensemble := ens
  Spec publicInput := ∃ execution, Executes publicInput execution
  soundness := soundness
  completeness := c.completeness

end Air.Flat
