import SP1Clean.FormalModel.Contracts.HostControl
import SP1Clean.Native.Operations.BoundedWord
import Clean.Gadgets.Equality

/-! # The native HALT host consumer

One row consumes one full instruction handoff and checks its canonical exit argument. There is
no padding and no additional Exit interaction: that contribution belongs to the instruction.
-/

namespace SP1Clean.HostHaltChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.call.code, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.call.result, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.call.length, const (0 : Word (ZMod p)))
  let _ ← BoundedWord.circuit (bound p) (by simp [bound]) ⟨input.call.arg1, input.comparison⟩
  HostCallChip.channel.pull input.call

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

end SP1Clean.HostHaltChip
