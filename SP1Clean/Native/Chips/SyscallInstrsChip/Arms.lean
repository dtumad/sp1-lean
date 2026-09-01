import SP1Clean.FormalModel.Contracts.SyscallInstrsChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `SyscallInstrs` row's arms, as bundled assertions

SP1's ECALL row dispatches on the syscall identifier, and each arm is an independent proof
boundary. Written inline, the row is a single do-block of some sixty assertions, and every
obligation about it — `localLength_eq`, the completeness closers, the requirement discharge — has
to normalise the whole block at once; that exceeds the elaboration budget, which this repository
does not raise. Bundling each arm as a `FormalAssertion` is Clean's own prescription for exactly
this ("bundle it if it is a proof boundary"), and it makes the parent's constraint list short
enough to reason about.

The regrouping changes neither the constraint list nor the interaction list the row emits, so the
faithfulness anchor is unaffected: `List.Forall (· = 0)` over a reassociated conjunction and
`List.Perm` over a reordered interaction list are the same propositions.

Contracts (`Inputs` and `Spec` per arm) live beside the chip's own in
`FormalModel/Contracts/SyscallInstrsChip.lean`; the proofs are in `Proofs/Chips/SyscallInstrsChip/`. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace PcArm

/-- The program-counter arm: `HALT` parks the machine at SP1's terminal `haltPc = (1, 0, 0)`;
every other arm falls through to `pc + 4`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.is_real * (((1 : Expression (ZMod p)) - input.is_halt) *
    (input.next_pc[0] - (input.pc[0] + 4))))
  assertZero (input.is_real * (((1 : Expression (ZMod p)) - input.is_halt) *
    (input.next_pc[1] - input.pc[1])))
  assertZero (input.is_real * (((1 : Expression (ZMod p)) - input.is_halt) *
    (input.next_pc[2] - input.pc[2])))
  assertZero (input.is_halt * (input.next_pc[0] - (1 : Expression (ZMod p))))
  assertZero (input.is_halt * input.next_pc[1])
  assertZero (input.is_halt * input.next_pc[2])

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end PcArm

end SP1Clean.SyscallInstrsChip
