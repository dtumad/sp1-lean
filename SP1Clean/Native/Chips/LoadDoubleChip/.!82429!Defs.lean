import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadDouble` chip row as a `GeneralFormalCircuit`

SP1's `LoadDouble` (LD): `rd ← mem[rs1 + signExtend(imm)]`, 8-byte aligned, full 64-bit word, no
sign-extension. Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8), the
`AddressOperation` gadget (address `= rs1 + imm` truncated to 48 bits, offset bits `0`), the
`MemoryAccess` primitive (a memory **read**: `new_value = prev_value`, at the computed 48-bit address),
and the `ITypeReader` adapter with the **loaded word** `memory_access.prev_value` as `op_a`'s write value.
Output is the extracted `Columns` struct.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven `is_real`-binary fact +
the `op_a != x0` gate; the load *meaning* (`rd = memory_access.prev_value`) is carried by the `ITypeReader`
sub-`Spec` (its write value is the loaded word). The bus's cross-row offline-memory meaning
(`prev_value = actual memory contents at the address`) is derived by
`Soundness/TypedMemory.lean`. -/

namespace SP1Clean.LoadDoubleChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadDouble-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.LoadDoubleChip.loadDoubleChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value (the
`op_b` register read), `op_c_imm` the sign-extended immediate; `state`/`adapter`/`memory_access` are the
committed CPUState / I-type-adapter / memory-access columns. The `address_operation` block is the
`AddressOperation` sub-circuit's witnessed output, not an input. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the four column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits `0` — LD is
8-byte aligned); `MemoryAccess` is a read (`new_value = prev_value`) at the 48-bit address; `ITypeReader`
writes the loaded word `memory_access.prev_value` to `op_a` (opcode `35 = LD`). The `op_a != x0` gate and
the `is_real` binary gate are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
