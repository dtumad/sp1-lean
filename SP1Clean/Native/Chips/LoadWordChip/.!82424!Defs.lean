import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
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

/-! # The `LoadWord` chip row as a `GeneralFormalCircuit`

SP1's `LoadWord` (LW / LWU): `rd ← mem[rs1 + signExtend(imm)]`, 4-byte aligned, the selected 32-bit
half of the read 64-bit word, sign-extended (LW) or zero-extended (LWU) to 64 bits. Composes — as Clean
sub-circuits — the `CPUState` reader (pc+4 / clk+8), the `AddressOperation` gadget (address
`= rs1 + imm` truncated to 48 bits, offset bit 2 = `offset_bit` — LW is 4-byte aligned), the
`MemoryAccess` primitive (a memory **read**: `new_value = prev_value`, at the 8-byte-aligned 48-bit
address), the `U16MSBOperation` gadget (the high bit `msb` of `selected_word[1]`, gated by `is_lw`),
and the `ITypeReader` adapter with the **sign/zero-extended loaded word**
`#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]` as `op_a`'s write value.

The SP1 memory **bus** access stays 8-byte-aligned: `MemoryAccess` sends/receives the full 4-limb
`prev_value`. The sub-word behaviour is in-circuit: `offset_bit` (bit 2 of the address) selects the
low (`prev_value[0..1]`) or high (`prev_value[2..3]`) 32-bit half into `selected_word`, and `msb`
drives the sign extension. Two selectors `is_lw` / `is_lwu` replace the single `is_real`
(`is_real = is_lw + is_lwu`); LW sign-extends, LWU zero-extends (`msb` zeroed by `(is_lw - 1)·msb`).

The chip `Spec` composes the sub-circuits' `Spec`s + the selection equations + the `op_a != x0` gate +
the selector binaries; the load meaning (`rd =` extended `selected_word`) is carried by `ITypeReader`'s
write value. The cross-row offline-memory meaning is derived by `Soundness/TypedMemory.lean`. -/

namespace SP1Clean.LoadWordChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadWord-chip row (Rust field order). The reader, memory, and sign-bit blocks reuse the
project substrate (`Extracted.AddressOperation`/`Extracted.U16MSBOperation` are still standalone
generated modules — the other loads/stores and the compare ops compose the same gadgets;
`Extracted.MemoryAccessCols` lives in the generated `MemoryAccess` struct carrier).
`Faithful.LoadWordChip.loadWordChipReconfigure` is the sole bridge to Rust's separately generated
whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  selected_word : Vector F 2
  msb : Extracted.U16MSBOperation F
  is_lw : F
  is_lwu : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The threaded reader column blocks + chip-specific witnesses. `state`/`adapter`/`memory_access` are the
committed column blocks; `offset_bit` is bit 2 of the address; `selected_word` the selected 32-bit half;
`msb` the witnessed high bit (via `U16MSBOperation.populate_msb`); `is_lw`/`is_lwu` the signed/unsigned
selectors. The `address_operation` block is the `AddressOperation` sub-circuit's witnessed output, not an
input. The rs1 base-address value (`op_b_val`) and the sign-extended immediate (`op_c_imm`) are **adapter
projections** (`adapter.op_b_memory.prev_value` / `adapter.op_c_imm`), not committed columns — SP1 reads
them from the I-type adapter. -/
structure Inputs (F : Type) where
  is_lw : F
  is_lwu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : F
  selected_word : fields 2 F
  msb : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- rs1 base-address value = the `op_b` register read (`op_b_memory.prev_value`). -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The sign-extended immediate = the I-type adapter's `op_c_imm`. -/
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_lw := Eval.eval env input.is_lw
         is_lwu := Eval.eval env input.is_lwu
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         selected_word := Eval.eval env input.selected_word
         msb := Eval.eval env input.msb } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The row selector `is_lw + is_lwu` (SP1's `is_real`). -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lw + input.is_lwu

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bit 2 =
`offset_bit`); `MemoryAccess` is a read at the 48-bit address; `U16MSBOperation` pins `msb` to the high
bit of `selected_word[1]` (gated by `is_lw`); `ITypeReader` writes the extended word to `op_a` (opcode
`31·is_lw + 34·is_lwu`). The four offset-selection gates, the `op_a != x0` gate, the `(is_lw-1)·msb`
zero-extension gate, and the `is_lw`/`is_lwu`/`is_real` binary gates are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_lw + input.is_lwu
  let _ ← Readers.CPUState.circuit
