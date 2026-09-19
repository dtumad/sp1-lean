import SP1Clean.FormalModel.Contracts.HostControl
import SP1Clean.Native.Operations.BoundedWord
import SP1Clean.Model.HostExit
import Clean.Gadgets.Equality

/-! # The native HALT host consumer

One row consumes one full instruction handoff and checks its canonical exit argument. There is
no padding. The instruction emits the public Exit value; this handler separately emits the
complete terminal receipt that authenticates optional outgoing status.
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
  HostExitBoundary.channel.push input.call.arg1

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

end SP1Clean.HostHaltChip
