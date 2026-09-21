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

/-! # The `StoreHalf` chip row as a `GeneralFormalCircuit`

SP1's `StoreHalf` (SH): `mem[rs1 + signExtend(imm)] ← rs2[15:0]`, 2-byte aligned. The **write**
