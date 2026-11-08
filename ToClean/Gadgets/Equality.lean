module

public import Clean.Gadgets.Equality
public import ToClean.Circuit.ComputableWitnesses

/-! # Computability of equality assertions

Missing upstream capability: an equality assertion has no witnesses, so its computability
requires no input-locality proof. This law lets the upstream tactic retain that small boundary
instead of transporting large assertion expressions. Intended for `Clean/Gadgets/Equality`.
-/

@[expose] public section

namespace Gadgets.Equality

variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

section
-- Match the instance captured by the polymorphic equality bundle.
local instance (priority := high + 1) : ProvableType (ProvablePair field field) := ProvablePair.instance

/-- Field-specialized metadata key for literal pairs of expressions. -/
@[circuit_norm ↓] theorem field_localLength (left right : Expression F) :
    (circuit field (F := F)).localLength (left, right) = 0 := rfl

/-- Field-specialized guarantee metadata for the same pair instance. -/
@[circuit_norm ↓] theorem field_channelsWithGuarantees :
    (circuit field (F := F)).channelsWithGuarantees = [] := rfl

/-- Field-specialized requirement metadata for the same pair instance. -/
@[circuit_norm ↓] theorem field_channelsWithRequirements :
    (circuit field (F := F)).channelsWithRequirements = [] := rfl

end

/-- An equality assertion generates no witnesses, independently of its inputs. -/
@[computable_witnesses ↓] theorem toSubcircuit_computableWitnesses
    (n : ℕ) (input : Var (ProvablePair M M) F) (env env' : ProverEnvironment F) :
    ((circuit M).toSubcircuit n input).ComputableWitnesses n env env' := by
  rcases input with ⟨left, right⟩
  simp only [Subcircuit.ComputableWitnesses, FormalAssertion.toSubcircuit,
    circuit, circuit_norm, Operations.forAll_toFlat_iff]
  change Operations.forAll n _ ((main (left, right)).operations n)
  simp only [main, circuit_norm]

end Gadgets.Equality
