import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReader
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `LoadByte` chip row as a `GeneralFormalCircuit`

SP1's `LoadByte` (LB / LBU): `rd ← mem[rs1 + signExtend(imm)]`, no alignment, the selected 8-bit byte of
the read 64-bit word, sign-extended (LB) or zero-extended (LBU) to 64 bits. Three offset bits select 1 of
8 bytes: `offset_bit[1..2]` pick the u16 limb (`selected_limb`), `offset_bit[0]` picks the low/high byte
within it. The byte is sub-limb-decomposed (`selected_limb = selected_limb_low_byte + 256·high`, both
U8-range-checked via an inline `ByteOpcode.U8Range` pair) and its sign bit `msb` is pinned by an inline
`ByteOpcode.MSB` byte-bus pull (gated by `is_lb`). The loaded word is
`#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (the byte sign-extends *within* limb 0).

Unlike `LoadWord`/`LoadHalf` (which compose `U16MSBOperation` as a sub-gadget), SP1 inlines the byte-bus
lookups, so this chip emits them directly via `byteChannel.pullIf` (witnessing nothing). -/

namespace SP1Clean.LoadByteChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadByte-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.LoadByteChip.loadByteChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : Vector F 3
  selected_limb : F
  selected_limb_low_byte : F
  selected_byte : F
  msb : F
  is_lb : F
  is_lbu : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

structure Inputs (F : Type) where
  is_lb : F
  is_lbu : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 3 F
  selected_limb : F
  selected_limb_low_byte : F
  selected_byte : F
  msb : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_lb := Eval.eval env input.is_lb
         is_lbu := Eval.eval env input.is_lbu
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit
         selected_limb := Eval.eval env input.selected_limb
         selected_limb_low_byte := Eval.eval env input.selected_limb_low_byte
         selected_byte := Eval.eval env input.selected_byte
         msb := Eval.eval env input.msb } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p := input.is_lb + input.is_lbu

/-- The sub-limb high byte `(selected_limb - selected_limb_low_byte)·256⁻¹` (over the field). -/
@[reducible] def highByte (input : Inputs (ZMod p)) : ZMod p :=
  (input.selected_limb - input.selected_limb_low_byte) * (256 : ZMod p)⁻¹

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_lb + input.is_lbu
  let high := (input.selected_limb - input.selected_limb_low_byte)
