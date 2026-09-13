import Clean.Circuit.Subcircuit

/-! # Assertion and lookup lists across a general subcircuit boundary

Clean already exposes `GeneralFormalCircuit.toSubcircuit_interactions`. The corresponding
assertion and lookup equalities are missing. These companions let a component extension preserve
the original algebra without unfolding a proof-bearing subcircuit inside its consumer. They are
intended for the same upstream module and require no application-specific assumptions.
-/

variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

theorem GeneralFormalCircuit.toSubcircuit_constraints
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.constraints (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.constraints) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat]

theorem GeneralFormalCircuit.toSubcircuit_lookups
    (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) (offset : ℕ) :
    FlatOperation.lookups (circuit.toSubcircuit offset input).ops.toFlat =
      (circuit.main input |>.operations offset |>.lookups) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Operations.lookups_toFlat]
