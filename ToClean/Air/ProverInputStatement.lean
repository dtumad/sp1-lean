module

public import ToClean.Air.EnsembleBuild

/-! # Raw statements after attaching private witness inputs

Clean's `withProverInput` configures the witness generator. The public verifier, physical
components and their ledger depend only on the underlying ensemble. This transports Clean's
raw statement in both directions with the same public input, physical rows and heights.
-/

public section

namespace Air.Flat.Ensemble

variable {F : Type} [FiniteField F] {PublicIO ProverInput : TypeMap}
  [ProvableType PublicIO] [ProvableType ProverInput]

/-- Attaching private input metadata preserves the raw public statement at every height vector. -/
theorem withProverInput_statement (ens : Ensemble F PublicIO) (hints : List HintTable)
    (balance : Balance F) (publicInput : PublicIO F) (heights : List ℕ) :
    (ens.withProverInput ProverInput hints).Statement balance publicInput heights ↔
      ens.Statement balance publicInput heights := by
  constructor <;> rintro ⟨fit, witness, header, sizes, constraints, balanced⟩
  · exact ⟨fit, witness.withEnsemble ens rfl, header, sizes, constraints, balanced⟩
  · exact ⟨fit, witness.withEnsemble (ens.withProverInput ProverInput hints) rfl,
      header, sizes, constraints, balanced⟩

end Air.Flat.Ensemble
