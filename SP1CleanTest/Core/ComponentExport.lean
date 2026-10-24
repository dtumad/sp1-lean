module

public import Clean.Backends.Plonky3.Print
public import SP1Clean.Model.Channels
public import SP1Clean.Model.SP1Field

/-! # Shared component-local export fixtures

Use Clean's built-in lowering, Rust emitter and preallocation for a production component.
External channels stay open: row comparisons do not establish ensemble balance.
-/

@[expose] public section

namespace SP1CleanTest.Core.ComponentExport

open Air.Flat SP1Clean

/-- The released SP1 field shared by native export fixtures and Rust comparisons. -/
abbrev Fp := ZMod SP1Prime

/-- A production component with its original constraints and channel interactions. -/
def ensemble (component : Component Fp) : Ensemble Fp unit where
  tables := [component]
  unique_names := by simp
  channels := [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
    Channels.memoryChannel.toRaw, Channels.programChannel.toRaw]

/-- The exporter requires a formal ensemble. Comparison fixtures deliberately make no public
semantic claim: their production circuits retain their proofs, and tests check the emitted rows.
A named hint table exposes the private input through Clean's built-in input representation. -/
def fixture {PublicIO : TypeMap} [ProvableType PublicIO]
    (ensemble : Ensemble Fp PublicIO) (Input : TypeMap := unit) [ProvableType Input] :
    FormalEnsemble Fp PublicIO where
  ensemble
  Spec _ := True
  soundness := fun _ _ _ => True.intro
  ProverInput := Input
  hintTables := [{ key := "input", width := size Input, offset := 0, rows := 1 }]

/-- A single independent component input, supplied through the fixture's named private hint. -/
def config (component : Component Fp)
    (padding : Array Fp := Array.replicate (size component.Input) 0) : WitnessGeneration.Config Fp where
  components := [(component.circuit.name, {
    mode := .preallocated {
      rows := 1
      input := .ofFExprs (Vector.ofFn fun column : Fin (size component.Input) =>
        .hintGet "input" (size component.Input) (.const 0) column)
      input_valid := by simp [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
        Witgen.VExpr.validForRow, Witgen.FExpr.validForRow,
        Witgen.U64Expr.validForRow, Witgen.RowProgram.Source.allowsHints]
      handlers := []
    }
    padding := { input := padding }
  })]
  fuel := 1

/-- Export a production circuit through Clean, with explicit padding where zeros are unsuitable. -/
def exportRust {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit Fp Input Output)
    (padding : Array Fp := Array.replicate (size Input) 0) : Except String String :=
  let component : Component Fp := { circuit, Assumptions := circuit.Assumptions }
  Backends.Plonky3.Print.ensembleToRust (fixture (ensemble component) Input) (config component padding)

end SP1CleanTest.Core.ComponentExport
