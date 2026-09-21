import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `StoreWord` chip row as a `GeneralFormalCircuit`

SP1's `StoreWord` (SW): `mem[rs1 + signExtend(imm)] ← rs2[31:0]`, 4-byte aligned. The **write**
counterpart of `LoadWord`. Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8),
the `AddressOperation` gadget (offset bit 2 = `offset_bit`), the `MemoryAccess` primitive (a memory
**write**: `new_value = store_value`, at the 8-byte-aligned 48-bit address), and the
`ITypeReaderImmutable` adapter (op_a = rs2 read, op_b = rs1 read, opcode `38 = SW`).

Because the memory bus access is 8-byte-aligned, `StoreWord` is a **read-modify-write**: `store_value`
merges the low two limbs of rs2 (`adapter.op_a_memory.prev_value[0..1]`) into the `offset_bit`-selected
half of the read `prev_value`, leaving the other half equal to `prev_value`. The bus receives the merged
8-byte `store_value`. -/

namespace SP1Clean.StoreWordChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native StoreWord-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.StoreWordChip.storeWordChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  store_value : Word F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value, `op_c_imm`
the immediate; `state`/`adapter`/`memory_access` are the committed column blocks; `offset_bit` is bit 2 of
the address; `store_value` the read-modify-write word actually written. The stored half is rs2's low two
limbs (`adapter.op_a_memory.prev_value[0..1]`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  store_value : (Word F)
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
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         store_value := Eval.eval env input.store_value } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bit 2 =
`offset_bit`); `MemoryAccess` is a write (`new_value = store_value`) at the 48-bit address;
`ITypeReaderImmutable` reads op_a (rs2) / op_b (rs1) (opcode `38 = SW`). The four read-modify-write
`store_value` merge gates and the `is_real` binary gate are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
