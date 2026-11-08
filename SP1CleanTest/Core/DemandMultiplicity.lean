import Clean.Air.WitnessGeneration
import Clean.Utils.Tactics
import SP1Clean.Model.SP1Field

/-! # Repeated demand with and without counted rows

Execution rows retain one occurrence per demand. Lookup providers may count repeated messages in
one row. Both use Clean's generator directly, including inactive padding and empty physical slots.
These executable checks exercise scheduling, not a general witness completeness theorem.
-/

namespace SP1CleanTest.Core.DemandMultiplicity

open Circuit Air.Flat

abbrev Fp := ZMod SP1Clean.SP1Prime

def values : Channel Fp field where
  name := "values"
  Guarantees _ _ := True

def main (counted : Bool) (input : Var (ProvablePair field field) Fp) : Circuit Fp Unit := do
  assertZero (.const (if counted then 0 else 1) * (input.2 * (input.2 - 1)))
  values.pushIf input.2 input.1

instance elaborated (counted : Bool) :
    ElaboratedCircuit Fp (ProvablePair field field) unit (main counted) := by
  elaborate_circuit

def provider (counted : Bool) (name : String) : GeneralFormalCircuit Fp (ProvablePair field field) unit where
  name
  main := main counted
  elaborated := elaborated counted
  Spec _ _ _ := True
  ProverAssumptions input _ _ := counted = true ∨ IsBool input.2
  channelsWithRequirements := [values.toRaw]
  requirementsChannelsLawful := by
    cases counted <;> intro input offset <;> simp [circuit_norm, main, values]
  soundness := by
    cases counted <;> circuit_proof_start [main, values]
  completeness := by
    cases counted <;> circuit_proof_start [main, values]
    · rw [← h_input] at h_assumptions
      simpa only [IsBool, mul_eq_zero, sub_eq_zero] using h_assumptions
    · simp

def component (counted unused : Bool) : Component Fp where
  circuit := provider counted (if unused then "unused" else "provider")
  generation := .demand {
    channel := values
    trigger := .pull
    guard _ := if unused then .false else .true
    input message := pure (.witness (.expr message), if counted then .multiplicity else 1)
  }

def requests (triple : Bool) : Verifier.Program Fp field where
  main value := do
    Verifier.pull values value
    Verifier.pull values value
    if triple then Verifier.pull values value
  Spec _ _ := True
  soundness := by intro _ _; trivial

def ensemble (counted triple : Bool) : Ensemble Fp field where
  tables := [component counted false, component counted true]
  unique_names := by simp [component, provider]
  channels := [values.toRaw]
  unique_channel_names := by simp
  verifier := requests triple
  tables_channels := by
    intro table member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      change [values.toRaw] ⊆ [values.toRaw]
      exact List.Subset.refl _
  verifier_channels := by
    cases triple <;> simp [requests, circuit_norm]

/-- Inspect actual physical rows after the canonical generator has balanced and padded them. -/
def generated (counted triple : Bool) : Except String (List Fp) :=
  match WitnessGeneration.generate (ensemble counted triple) 32 7 () with
  | .error error => .error (toString error)
  | .ok witness => do
    unless WitnessGeneration.constraintsHold witness && WitnessGeneration.channelsBalanced witness do
      throw "generated witness failed constraints or channel balance"
    match witness.tables with
    | [active, unused] =>
      unless unused.table.isEmpty do
        throw "unused component acquired rows"
      pure (active.table.map fun row => row[1]!)
    | _ => throw "unused component lost its physical table slot"

example : generated false false = .ok [1, 1] := by native_decide
example : generated true false = .ok [2] := by native_decide
example : generated false true = .ok [1, 1, 1, 0] := by native_decide
example : generated true true = .ok [3] := by native_decide

end SP1CleanTest.Core.DemandMultiplicity
