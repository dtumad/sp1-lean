import Clean.Air.FlatComponent

/-! # Decoding a component output through its formal circuit metadata

## Gap against upstream

Clean defines `Component.rowOutput` through a subcircuit application, but has no constructor
equation exposing the formal circuit's declared output. This rewrite keeps concrete witness
programs opaque when a client relates physical row outputs to a circuit's interaction ledger.
-/

namespace Air.Flat.Component

open Circuit

variable {F : Type} [FiniteField F] {Input Output : TypeMap}
variable [ProvableType Input] [ProvableType Output]

theorem rowOutput_mk (circuit : GeneralFormalCircuit F Input Output) (env : Environment F) :
    (⟨circuit⟩ : Component F).rowOutput env =
      eval env (circuit.output (varFromOffset Input 0) (size Input)) := rfl

end Air.Flat.Component
