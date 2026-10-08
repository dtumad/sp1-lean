import Clean.Air.Extraction.Rust
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Proofs.Chips.LoadByteChip.Formal
import SP1Clean.Proofs.Chips.DivRemChip.Complete
import SP1Clean.Proofs.Chips.MulChip.Complete
import SP1Clean.Proofs.Chips.BitwiseChip.Complete
import SP1Clean.Proofs.Chips.LtChip.Complete
import SP1Clean.Model.SP1Field

/-! # Instruction-local Rust export

Export production instruction components through Clean's built-in lowering and Rust emitter.
Each surrounding singleton has no providers: its channels remain open, so it is a row-level
comparison fixture, not an executable SP1 ensemble or a proof of global balance.
-/

namespace SP1CleanTest.Core.InstructionExport

open Air.Flat SP1Clean

abbrev Fp := ZMod SP1Prime

/-- An instruction component with its original constraints and channel interactions. -/
def ensemble (component : Component Fp) : Ensemble Fp unit where
  tables := [component]
  unique_names := by simp
  channels := [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
    Channels.memoryChannel.toRaw, Channels.programChannel.toRaw]

/-- A single independent instruction input, supplied as prover construction data. -/
def config (Inputs : Type → Type) [ProvableType Inputs] : WitnessGeneration.Config Fp Inputs where
  modes := [.preallocated {
    rows := 1
    input := {
      width := size Inputs
      steps := []
      output := .mapRange (size Inputs) (.proverInputGet .idx)
    }
    input_valid := by rfl
    handlers := []
  }]
  padding := [{ input := Array.replicate (size Inputs) 0 }]
  fuel := 1

/-- Both AIR and witness functions come from Clean; no local expression renderer is involved. -/
def addRust : Except String String :=
  Extraction.Rust.ensembleToRust "AddInstruction"
    (ensemble { circuit := AddChip.circuit }) (config AddChip.Inputs)

/-- Export LB/LBU, including its witnessed address and RAM interactions. -/
def loadByteRust : Except String String :=
  Extraction.Rust.ensembleToRust "LoadByteInstruction"
    (ensemble { circuit := LoadByteChip.circuit }) (config LoadByteChip.Inputs)

/-- Export all eight division/remainder variants using explicit selectors and DIVU padding. -/
def divRemRust : Except String String :=
  Extraction.Rust.ensembleToRust "DivRemInstruction"
    (ensemble { circuit := DivRemChip.circuit })
    ({ config DivRemChip.Inputs with
      padding := [{ input := (toElements (TraceGen.divRemPaddingInputs (p := SP1Prime))).toArray }] } :
      WitnessGeneration.Config Fp DivRemChip.Inputs)

/-- Export all five multiply variants with explicit selectors and zero padding. -/
def mulRust : Except String String :=
  Extraction.Rust.ensembleToRust "MulInstruction"
    (ensemble { circuit := MulChip.circuit }) (config MulChip.Inputs)

/-- Export XOR/OR/AND with explicit selectors and zero padding, including immediate operands. -/
def bitwiseRust : Except String String :=
  Extraction.Rust.ensembleToRust "BitwiseInstruction"
    (ensemble { circuit := BitwiseChip.circuit }) (config BitwiseChip.Inputs)

/-- Export SLT/SLTU with explicit selectors and zero padding, including immediate operands. -/
def ltRust : Except String String :=
  Extraction.Rust.ensembleToRust "LtInstruction"
    (ensemble { circuit := LtChip.circuit }) (config LtChip.Inputs)

end SP1CleanTest.Core.InstructionExport
