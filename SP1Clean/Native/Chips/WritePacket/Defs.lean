import SP1Clean.FormalModel.Contracts.WritePacket
import SP1Clean.Native.Operations.ClockParts

/-! # Native WRITE packet header

The instruction, x12 observation and packet share the same timestamp limbs. A normalized
WRITE code and return are built into the instruction request. The original widths remain
checked on every row before either clock is recombined.
-/

namespace SP1Clean.WritePacket

open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Consume the WRITE and its x12 observation and supply the resulting packet header. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion ClockParts.circuit input.timestamp
  HostCallChip.channel.pull input.call
  WriteProbe.readChannel.pull input.read
  channel.push input.header

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

end SP1Clean.WritePacket
