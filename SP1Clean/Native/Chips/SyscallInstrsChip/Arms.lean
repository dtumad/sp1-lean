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

namespace CommitArm

/-- The bitmap's sum, as a circuit expression. -/
@[circuit_norm] def bitSumVar (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.index_bits[0] + input.index_bits[1] + input.index_bits[2] + input.index_bits[3] +
    input.index_bits[4] + input.index_bits[5] + input.index_bits[6] + input.index_bits[7]

/-- The commit arms: a one-hot index bitmap whose set position is `a0`'s low limb, and `a1`
carrying the selected digest word packed two bytes to a limb. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.is_real * (input.index_bits[0] *
    (input.index_bits[0] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[1] *
    (input.index_bits[1] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[2] *
    (input.index_bits[2] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[3] *
    (input.index_bits[3] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[4] *
    (input.index_bits[4] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[5] *
    (input.index_bits[5] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[6] *
    (input.index_bits[6] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[7] *
    (input.index_bits[7] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * ((input.is_commit + input.is_commit_deferred) *
    (bitSumVar input - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (((1 : Expression (ZMod p)) -
    (input.is_commit + input.is_commit_deferred)) * bitSumVar input))
  assertZero (input.is_real * (input.index_bits[0] *
    (input.op_b[0] - (0 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[1] *
    (input.op_b[0] - (1 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[2] *
    (input.op_b[0] - (2 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[3] *
    (input.op_b[0] - (3 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[4] *
    (input.op_b[0] - (4 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[5] *
    (input.op_b[0] - (5 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[6] *
    (input.op_b[0] - (6 : Expression (ZMod p)))))
  assertZero (input.is_real * (input.index_bits[7] *
    (input.op_b[0] - (7 : Expression (ZMod p)))))
  assertZero (input.is_real * ((input.is_commit + input.is_commit_deferred) *
    (input.op_b[1] + input.op_b[2] + input.op_b[3])))
  assertZero (input.is_real * (input.is_commit *
    ((input.digest_word[0] + input.digest_word[1] * (256 : Expression (ZMod p))) - input.op_c[0])))
  assertZero (input.is_real * (input.is_commit *
    ((input.digest_word[2] + input.digest_word[3] * (256 : Expression (ZMod p))) - input.op_c[1])))
  assertZero (input.is_real * (input.is_commit * input.op_c[2]))
  assertZero (input.is_real * (input.is_commit * input.op_c[3]))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end CommitArm

end SP1Clean.SyscallInstrsChip
