module

public import Clean.Air.FlatComponent
public import ToClean.Air.TableBuild

/-! # Decoding a component output through its formal circuit metadata

## Gap against upstream

Clean defines `Component.rowOutput` through a subcircuit application, but has no constructor
equation exposing the formal circuit's declared output. This rewrite keeps concrete witness
programs opaque when a client relates physical row outputs to a circuit's interaction ledger.
The congruence theorem records that decoding depends on committed cells, not prover data.
-/

@[expose] public section

namespace Air.Flat.Component

open Circuit

variable {F : Type} [FiniteField F]

theorem rowOutput_eq (component : Component F) (env : Environment F) :
    component.rowOutput env =
      eval env (component.circuit.output (varFromOffset component.Input 0)
        (size component.Input)) := rfl

/-- Equal committed cells decode to the same output, independently of the data environment. -/
theorem rowOutput_congr (component : Component F) {env env' : Environment F}
    (same : env.get = env'.get) : component.rowOutput env = component.rowOutput env' := by
  have values : Expression.eval env = Expression.eval env' :=
    funext (Expression.eval_congr same)
  simp only [rowOutput, CircuitType.eval_var, ProvableType.eval, values]

end Air.Flat.Component
