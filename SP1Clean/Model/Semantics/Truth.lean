import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Semantics.Decode

/-! # Execution truth — conclusions of global grounding

These predicates describe how structural bus records are interpreted after balance and timing have
been established. They are deliberately not Clean channel guarantees: a row-local sender cannot prove
reachability, ROM commitment, or last-write currency.

There are two intentionally distinct execution scopes:

- `ExecutionStateTruth` is boot-relative and parameterized by a fixed `SP1MachineModel`. It belongs at
  the composed-execution boundary, where a shard has been anchored in the model-selected boot run.
- `LocalStateTruth`/`LocalValueAt`/`LocalMemTruth` are relative to one selected shard initial state and
  public initial clock. They are the canonical predicates for AIR grounding. A shard-local theorem must
  not silently require that its public initial state is a zero-register boot state.

`RowFacts`/`LocalStepFact` form the chip-agnostic per-row advance obligation: from the pulled state's
truth and engine-supplied current operand truths, the pushed state and written values are true. -/

open LeanRV64D
namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The per-row advance obligation -/

/-- The chip-agnostic facts one real row contributes, in bus-message form: its state pull/push, its
pinned-opcode fetch, its memory read-priors (each with the micro-time at which the row *reads* — the
currency point), and its memory pushes (read-backs and writes). -/
structure RowFacts (p : ℕ) where
  statePull : StateMsg (ZMod p)
  statePush : StateMsg (ZMod p)
  fetch : ProgramMsg (ZMod p)
  /-- read-prior messages, paired with the row-local micro-time of the read. -/
  memPulls : List (MemoryMsg (ZMod p) × ℕ)
  memPushes : List (MemoryMsg (ZMod p))

/-! ## Committed-program grounding -/

/-- A Program-bus message projected to the committed program-row column shape — a trivial field-rename now
that `ProgramMsg.op_b`/`op_c` are already `Word`s — so `decodedInROM` can be applied to a `ProgramMsg`. -/
def rowOfMsg (m : ProgramMsg (ZMod p)) : SP1Clean.ProgramChip.ProgramRow (ZMod p) where
  pc0 := m.pc0
  pc1 := m.pc1
  pc2 := m.pc2
  opcode := m.opcode
  op_a := m.op_a
  op_b := m.op_b
  imm_b := m.imm_b
  op_c := m.op_c
  op_a_0 := m.op_a_0
  imm_c := m.imm_c

end SP1Clean.Semantics
