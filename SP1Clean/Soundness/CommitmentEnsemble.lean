import SP1Clean.Native.Operations.CommitmentStatement
import SP1Clean.Native.Operations.CommitmentBoundary

/-! # Installing the immutable commitment statement

The fixed declaration provider and public assertions share one verifier-owned statement.
Existing physical positions are preserved. The new table uses Clean's ordinary preprocessed
payload provider; neither the prover's mutable bank nor per-call PublicValues echoes select it.
-/

namespace SP1Clean.Soundness.CommitmentEnsemble

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- Append the provider, retaining every original row, channel occurrence and table position. -/
def withSource (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO where
  tables := base.tables ++ [CommitmentDeclaration.source statement]
  unique_names := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append] using base.unique_names.concat fresh
  channels := base.channels ++ [CommitmentDeclaration.channel.toRaw]
  verifier := base.verifier

/-- Public bytes, deferred elements and flags are bound to the same fixed provider. -/
def install (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO :=
  (CommitmentBoundary.checker statement).install (withSource statement base fresh)

end SP1Clean.Soundness.CommitmentEnsemble
