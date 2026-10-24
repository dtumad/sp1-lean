import SP1Clean.FormalModel.Contracts.HostRamRead
import SP1Clean.Proofs.Chips.HostRamAccessChip.Formal

/-! # Read-only host RAM provider

The underlying access's coordination push is consumed internally. One unit push serves the
logical read, preserving the physical interaction count used by the balance argument.
-/

namespace SP1Clean.HostRamReadChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← HostRamAccessChip.circuit input.ram
  assertion (Gadgets.Equality.circuit Word) (input.ram.new_value, input.ram.access.prev_value)
  HostRamAccessChip.channel.pull input.ram.message
  channel.push input.message

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

end SP1Clean.HostRamReadChip
