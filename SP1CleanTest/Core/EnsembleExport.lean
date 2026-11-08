import SP1CleanTest.Core.ComponentExport
import ToClean.Air.MessageIndex
import SP1CleanTest.Core.EnsembleCheck

/-! # Built-in Rust export of fixed membership and a public boundary

The legacy lookup fixture's allowed values become verifier-fixed columns. Clean owns lowering,
Rust rendering and witness scheduling. The finite checker independently checks the generated
physical rows and the separate public verifier; generation is not a completeness theorem.
-/

namespace SP1CleanTest.Core.EnsembleExport

open Air.Flat Circuit
open EnsembleCheck (Fp values verifier)

/-- A fixed allowed value, its request count and a constrained generated square. -/
def provider : GeneralFormalCircuit Fp fieldPair field where
  name := "allowed"
  main input := do
    let square ← witness (.expr (input.1 * input.1) : Witgen.FExpr Fp)
    assertZero (square - input.1 * input.1)
    values.emit input.2 input.1
    return square
  Spec input output _ := output = input.1 * input.1
  channelsWithRequirements := [values.toRaw]
  soundness := by
    circuit_proof_start [EnsembleCheck.values]
    rw [← h_input]
    exact sub_eq_zero.mp h_holds
  completeness := by
    circuit_proof_start [EnsembleCheck.values]
    simp_all

/-- The value is verifier-fixed and the count belongs to upstream preallocation. -/
def component : Component Fp where
  circuit := provider
  generation := .preallocated {
    channel := values
    trigger := .pull
    height := 2
    input index := pure (.fixed (.listGet [.const 7, .const 9] index), .multiplicity)
    rowOf _ := .messageIndex [#v[7], #v[9]] 0 2
  }

/-- One physical provider with the original separate public pull. -/
def ensemble : Ensemble Fp field where
  tables := [component]
  unique_names := by simp
  channels := [values.toRaw]
  verifier := verifier
  unique_channel_names := by simp
  tables_channels := by
    intro component member
    obtain rfl := List.mem_singleton.mp member
    change [values.toRaw] ⊆ _
    simp
  verifier_channels := by
    intro channel member
    simpa [EnsembleCheck.verifier, Verifier.Program.channels,
      Verifier.Program.channelsWithGuarantees, Verifier.Program.channelsWithRequirements,
      Verifier.Program.operations, circuit_norm] using member

/-- Independent raw acceptance includes all occurrences, including the unused fixed row. -/
def description : Air.Flat.EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, component, Component.lookups_eq, Component.rowOperations, provider, circuit_norm]
/-- Use Clean's scheduler with no external prover input or custom witness evaluator. -/
def generate (value : Fp) : Except String (EnsembleWitness ensemble) :=
  WitnessGeneration.generate ensemble 8 value () |>.mapError toString

/-- The entire output is rendered by Clean's built-in exporter. -/
def rust : Except String String :=
  Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture ensemble) 8

/-- Check generation against raw constraints and the full ledger. -/
def accepts (value : Fp) : Bool :=
  match generate value with
  | .ok witness => description.checkWitness witness
  | .error _ => false

/-- Both original allowed values pass, while the forged member has no fixed provider. -/
theorem membership_cases : [accepts 7, accepts 9, accepts 8] = [true, true, false] := by
  native_decide

/-- Lowering and Rust rendering both succeed on the fixed-column representation. -/
theorem export_succeeds : rust.isOk = true := by native_decide

end SP1CleanTest.Core.EnsembleExport
