import SP1Clean.FormalModel.Contracts.HostControl
import Clean.Gadgets.Equality

/-! # No-effect constrained-replay host calls

Consume the full instruction handoff with the canonical code and its released return. Arguments are
unused by this call and stay unrestricted. All fields are supplied by the matched instruction.
-/

namespace SP1Clean.HostNoopChip

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- Authenticate the full code and return value, then pull the instruction handoff. -/
def main (kind : Kind) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.code, const (codeWord kind))
  assertion (Gadgets.Equality.circuit Word) (input.result, const (resultWord kind))
  HostCallChip.channel.pull input

instance elaborated (kind : Kind) : ElaboratedCircuit (ZMod p) Inputs unit (main kind) := by
  elaborate_circuit

end SP1Clean.HostNoopChip
