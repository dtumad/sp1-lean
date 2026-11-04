import Clean.Backends.Plonky3.Print
import SP1Clean.Model.SP1Field

/-! # Shared component-local export fixtures

Circuit comparisons lower the production row through Clean's existing component lowering and
Rust printer. Rust supplies the input cells and calls `complete_row`; there is no claim that an
isolated row balances its external channels. Ensemble fixtures use the complete upstream
lowering and scheduler separately.
-/

namespace SP1CleanTest.Core.ComponentExport

open Air.Flat SP1Clean

/-- The released SP1 field shared by native export fixtures and Rust comparisons. -/
abbrev Fp := ZMod SP1Prime

/-- Row-only fixtures never ask the scheduler to create a row. Their inputs are supplied directly
by the comparison harness before calling upstream witness completion. -/
def component {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit Fp Input Output)
    (padding : Array Fp := Array.replicate (size Input) 0) : Component Fp where
  circuit
  Assumptions := circuit.Assumptions
  generation := .demand {
    channel := ({ name := "component.fixture", Guarantees _ _ := True } : Channel Fp unit)
    trigger := .pull
    guard _ := .false
    input _ := pure (fromElements (Vector.ofFn fun column : Fin (size Input) =>
      .witness (.hintGet "input" (size Input) (.const 0) column)))
    padding := fromElements (Vector.ofFn fun column => padding[column.val]?.getD 0)
  }

/-- These exported test ensembles make no public semantic claim. Their complete production
circuits and registries are retained; native witness and Rust comparisons are executable tests. -/
def fixture {PublicIO : TypeMap} [ProvableType PublicIO]
    (ensemble : Ensemble Fp PublicIO) : FormalEnsemble Fp PublicIO .logUp where
  ensemble
  Spec _ := True
  soundness := fun _ _ _ _ => True.intro

/-- Lower a production row with upstream code and print a component-comparison program.
The disabled demand mode contains no fixed or count cells; full ensemble generation is tested
through `ensembleToRust` elsewhere. -/
def exportRust {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit Fp Input Output)
    (padding : Array Fp := Array.replicate (size Input) 0) : Except String String := do
  let row := component circuit padding
  let lowered ← Backends.lowerComponent 0 row |>.mapError toString
  let mode ← Backends.lowerGeneration 0 row none |>.mapError toString
  return Backends.Plonky3.Print.programToRustFile {
    publicInputWidth := 0
    proverInputWidth := size Input
    hintTables := [{ key := "input", width := size Input, offset := 0, rows := 1 }]
    components := [lowered]
    verifierInteractions := []
    modes := [mode]
    fuel := 1
  }

end SP1CleanTest.Core.ComponentExport
