import Clean.Air.Extraction.Rust
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Model.SP1Field

/-! # Instruction-local Rust export

Export the actual ADD component through Clean's built-in lowering and Rust emitter.
The surrounding singleton has no providers: its channels remain open, so it is a row-level
comparison fixture, not an executable SP1 ensemble or a proof of global balance.
-/

namespace SP1CleanTest.Core.InstructionExport

open Air.Flat SP1Clean

abbrev Fp := ZMod SP1Prime

/-- The production ADD circuit with its original constraints and channel interactions. -/
def ensemble : Ensemble Fp unit where
  tables := [{ circuit := AddChip.circuit }]
  unique_names := by simp
  channels := [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
    Channels.memoryChannel.toRaw, Channels.programChannel.toRaw]

/-- A single independent instruction input, supplied as prover construction data. -/
def config : WitnessGeneration.Config Fp AddChip.Inputs where
  modes := [.preallocated {
    rows := 1
    input := .ofFExprs (Vector.ofFn fun i : Fin (size AddChip.Inputs) =>
      .proverInputGet (.const i.val.toUInt64))
    input_valid := by rfl
    handlers := []
  }]
  padding := [{ input := Array.replicate (size AddChip.Inputs) 0 }]
  fuel := 1

/-- Both AIR and witness functions come from Clean; no local expression renderer is involved. -/
def rust : Except String String :=
  Extraction.Rust.ensembleToRust "AddInstruction" ensemble config

end SP1CleanTest.Core.InstructionExport
