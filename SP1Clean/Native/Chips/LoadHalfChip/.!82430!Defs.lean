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

/-! # The `LoadHalf` chip row as a `GeneralFormalCircuit`

SP1's `LoadHalf` (LH / LHU): `rd ← mem[rs1 + signExtend(imm)]`, 2-byte aligned, the selected 16-bit
limb of the read 64-bit word, sign-extended (LH) or zero-extended (LHU) to 64 bits. The direct sub-word
analogue of `LoadWord`: two offset bits `offset_bit[0..1]` (bits 1–2 of the address) select 1 of the 4
u16 limbs of `prev_value` into the single 16-bit `selected_half`; the `U16MSBOperation` gadget pins the
high bit `msb` of `selected_half` (gated by `is_lh`) to drive the sign extension. The loaded word is
`#v[selected_half, 65535·msb, 65535·msb, 65535·msb]`.

The SP1 memory **bus** access stays 8-byte-aligned: `MemoryAccess` sends/receives the full 4-limb
`prev_value`. Two selectors `is_lh` / `is_lhu` replace the single `is_real` (`is_real = is_lh + is_lhu`);
LH sign-extends, LHU zero-extends (`msb` zeroed by `is_lhu·msb`). The cross-row offline-memory meaning
is derived by `Soundness/TypedMemory.lean`. -/

namespace SP1Clean.LoadHalfChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadHalf-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` / `Extracted.U16MSBOperation` are still standalone generated
modules — the other loads and stores compose the same gadgets; `Extracted.MemoryAccessCols` lives in
the generated `MemoryAccess` struct carrier). `Faithful.LoadHalfChip.loadHalfChipReconfigure` is the
sole bridge to Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : Vector F 2
  selected_half : F
  msb : Extracted.U16MSBOperation F
  is_lh : F
  is_lhu : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value, `op_c_imm`
the sign-extended immediate; `state`/`adapter`/`memory_access` are the committed column blocks; `offset_bit`
are bits 1–2 of the address; `selected_half` the selected 16-bit limb; `msb` the witnessed high bit (via
`U16MSBOperation.populate_msb`); `is_lh`/`is_lhu` the signed/unsigned selectors. -/
structure Inputs (F : Type) where
  is_lh : F
  is_lhu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 2 F
  selected_half : F
  msb : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_lh := Eval.eval env input.is_lh
         is_lhu := Eval.eval env input.is_lhu
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         selected_half := Eval.eval env input.selected_half
         msb := Eval.eval env input.msb } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The row selector `is_lh + is_lhu` (SP1's `is_real`). -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lh + input.is_lhu

/-- Compose the column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits 1–2 =
`offset_bit[0..1]`, bit 0 = 0 since LH is 2-byte aligned); `MemoryAccess` is a read at the 48-bit
address; `U16MSBOperation` pins `msb` to the high bit of `selected_half` (gated by `is_lh`); `ITypeReader`
writes the extended word to `op_a` (opcode `30·is_lh + 33·is_lhu`). The four 2-bit offset-selection gates,
the `op_a != x0` gate, the `is_lhu·msb` zero-extension gate, and the binary gates are imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_lh + input.is_lhu
  let _ ← Readers.CPUState.circuit
