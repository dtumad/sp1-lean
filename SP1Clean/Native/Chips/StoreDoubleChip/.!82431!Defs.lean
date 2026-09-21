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

/-! # The `StoreDouble` chip row as a `GeneralFormalCircuit`

SP1's `StoreDouble` (SD): `mem[rs1 + signExtend(imm)] ← rs2`, 8-byte aligned, full 64-bit word. The
**write** counterpart of `LoadDouble`. Composes — as Clean sub-circuits — the `CPUState` reader
(pc+4 / clk+8), the `AddressOperation` gadget (address `= rs1 + imm` truncated to 48 bits, offset bits
`0`), the `MemoryAccess` primitive (a memory **write**: `new_value = rs2`, at the computed 48-bit
address), and the `ITypeReaderImmutable` adapter (op_a = rs2 **read**, op_b = rs1 read, op_c the
immediate). Output is the native `Columns` struct.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven `is_real`-binary fact;
the store *meaning* (the new memory word pushed at the address is the rs2 word
`adapter.op_a_memory.prev_value`) is carried by `MemoryAccess`'s `new_value` input being the rs2 read
value, with the bus's cross-row offline-memory meaning derived by `Soundness/TypedMemory.lean`.
