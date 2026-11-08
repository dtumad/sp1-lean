import SP1Clean.Proofs.Operations.OrdinaryObservation
import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import SP1Clean.Proofs.Chips.StateBumpChip.Formal
import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal
import SP1Clean.Proofs.Chips.HaltChip.Witgen
import Clean.Circuit.Theorems
import Clean.Circuit.Subcircuit
import ToClean.Gadgets.BitwiseByte

/-! # Constructing physical ordinary observation rows

The standard Clean table builder uses the same local population and witness IR as the circuit.
Computability comes from the bundled circuit proof. Clock order
is a semantic input condition for this subsystem; the mixed compiler derives it from execution.
-/

namespace SP1Clean

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The composed word gadgets require only the weaker field bound. -/
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

namespace OrdinaryObservation

variable {generation : WitnessGeneration.DemandMode (ZMod p) Inputs}

/-- The standard table builder preserves every supplied observation input within Clean's physical
row-index capacity. This is a table representation bound, separate from execution semantics. -/
def construct (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray) : Table (ZMod p) :=
  Table.build { circuit := circuit enabled, generation := .demand generation, Assumptions := (circuit enabled).Assumptions }
    inputs data (ProverHint.empty (ZMod p)) bounded (by trivial) consistent

/-- Semantic observation inputs construct all physical constraints. -/
theorem construct_constraints (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray)
    (valid : ∀ input ∈ inputs, Spec enabled input) : (construct (generation := generation) enabled inputs data bounded consistent).Constraints :=
  Table.build_constraints _ _ _ _ bounded _ consistent valid

/-- Generated rows also supply every local channel guarantee, including all counter Byte checks. -/
theorem construct_guarantees (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray)
    (valid : ∀ input ∈ inputs, Spec enabled input) : (construct (generation := generation) enabled inputs data bounded consistent).Guarantees :=
  Table.build_guarantees _ _ _ _ bounded _ consistent valid

/-- Physical height is exactly the supplied observation count. -/
theorem construct_length (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray) :
    (construct (generation := generation) enabled inputs data bounded consistent).length = inputs.length := List.length_map ..

/-- Reading the generated physical rows recovers the exact supplied observation inventory. -/
theorem construct_inputs (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data evaluationData : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray) :
    (construct (generation := generation) enabled inputs data bounded consistent).table.map (fun physical =>
      valueFromOffset Inputs 0 (Environment.fromArray physical evaluationData)) = inputs := by
  simp only [construct, Table.build, List.map_map]
  have decode (input : Inputs (ZMod p)) :=
    Component.rowInput_buildRow ({ circuit := circuit enabled, generation := .demand generation, Assumptions := (circuit enabled).Assumptions } : Component (ZMod p)) input data evaluationData (ProverHint.empty _)
  change inputs.map (fun input => ({ circuit := circuit enabled, generation := .demand generation, Assumptions := (circuit enabled).Assumptions } : Component (ZMod p)).rowInput
    (Environment.fromArray (({ circuit := circuit enabled, generation := .demand generation, Assumptions := (circuit enabled).Assumptions } : Component (ZMod p)).buildRow input data (ProverHint.empty _)) evaluationData)) = inputs
  simp only [decode, List.map_id']

/-- Constructed consumers pull precisely the supplied receipt sequence. -/
theorem construct_receipts (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray) :
    (construct (generation := generation) enabled inputs data bounded consistent).interactionsWith InstructionReceipt.channel.toRaw =
      inputs.map (fun input => InstructionReceipt.channel.pulledValue input.receipt) := by
  have decoded := congrArg (List.map fun input => InstructionReceipt.channel.pulledValue input.receipt)
    (construct_inputs (generation := generation) enabled inputs data data bounded consistent)
  simp only [Table.interactionsWith, Table.environment, construct, Table.build, receipt_values]
  rw [← List.map_eq_flatMap]
  simpa only [List.map_map, Function.comp_def, construct, Table.build] using decoded

/-- Constructed observation links preserve each supplied previous/next pair literally. -/
theorem construct_states (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (consistent : data.tables (circuit (p := p) enabled).name (size Inputs) = (inputs.map toElements).toArray) :
    (construct (generation := generation) enabled inputs data bounded consistent).interactionsWith stateChannel.toRaw = inputs.flatMap (fun input =>
      [stateChannel.pulledValue input.previous, stateChannel.pushedValue input.next]) := by
  have decoded := congrArg (List.flatMap fun input =>
    [stateChannel.pulledValue input.previous, stateChannel.pushedValue input.next])
    (construct_inputs (generation := generation) enabled inputs data data bounded consistent)
  simpa only [Table.interactionsWith, Table.environment, construct, Table.build, state_values,
    List.flatMap_map] using decoded

end OrdinaryObservation
end SP1Clean
