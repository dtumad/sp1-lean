import SP1Clean.Math.Word
import SP1Clean.Extracted.SystemOracle.SyscallInstrs
import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.FormalModel.Contracts.Operations
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # System-table chip contract: the `SyscallInstrs` row

The `Inputs` row struct of SP1's ECALL table (`../sp1 crates/core/machine/src/syscall/instructions`),
the native replacement for today's single-arm `HaltChip`.

**Why the whole table rather than one arm.** `ChipFaithful` equates two *complete* assertion systems
and interaction multisets, so an anchor between one arm and SP1's multi-arm dispatcher is not a
statable theorem. Modelling the full row is also *cheaper* than the alternative: SP1's syscall id is
little-endian `| ID | Table | unused | unused |`, and byte 1 — "the handler of this system call has
its own table" (`crates/core/executor/src/syscall_code.rs`) — is exactly the multiplicity of the
row's send on `Channels.syscallChannel`. Declaring that channel with no provider makes balance force
the byte to zero, so "the supported profile runs no precompiles" becomes a theorem instead of an
assumption, and the excluded `SyscallCore` table need not be modelled at all.

**Field order is load-bearing.** The fields below are laid out in the flat upstream column order of
`Extracted.SyscallInstrsCols` (65 cells, `CoreProfile.Table.width .syscallInstrs`), so the
faithfulness codec is a near-identity re-grouping rather than a permutation. `inputs_size` pins the
count; if a field is added, moved, or resized, that theorem is what fails.

Column map, with the upstream indices each field occupies:

| cells | field | upstream |
|---|---|---|
| 6 | `state` | `[0..5]` — `clk_high`, the two clock limbs, `pc` |
| 1 + 6 | `op_a`, `op_a_memory` | `[6]`, `[7..12]` — `t0`, holding the syscall id |
| 1 | `op_a_unchanged` | `[13]` — gates "`op_a` keeps its value" |
| 1 + 6 | `op_b`, `op_b_memory` | `[14]`, `[15..20]` — `a0`: exit code, or commit index |
| 1 + 6 | `op_c`, `op_c_memory` | `[21]`, `[22..27]` — `a1`: the commit digest word |
| 3 | `next_pc` | `[28..30]` |
| 1 | `is_halt` | `[31]` — already multiplied by `is_real` |
| 4 | `op_a_value` | `[32..35]` — `op_a` *after* the syscall |
| 4 | `syscall_id_bytes` | `[36..39]` — the id's byte split |
| 2 × 5 | the five arm selectors | `[40..49]` |
| 8 | `digest_index_bits` | `[50..57]` — one-hot over the 8 digest words |
| 4 | `digest_word` | `[58..61]` — the selected word, cached |
| 1 + 1 | `op_b_cmp`, `op_c_cmp` | `[62]`, `[63]` — valid-field-element bounds |
| 1 | `is_real` | `[64]` |

The five selectors are `IsZeroOperation` blocks on the identifier byte, at SP1's canonical codes:
`0` HALT, `3` `ENTER_UNCONSTRAINED`, `16` `COMMIT`, `26` `COMMIT_DEFERRED_PROOFS`, `240` `HINT_LEN`.
Every other identifier is a *generic* syscall, dispatched over the syscall bus. -/

namespace SP1Clean.SyscallChip

open SP1Clean.Extracted

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's `SyscallCode::HALT`. -/
def haltCode : ℕ := 0

/-- SP1's `SyscallCode::ENTER_UNCONSTRAINED`. -/
def enterUnconstrainedCode : ℕ := 3

/-- SP1's `SyscallCode::COMMIT`. -/
def commitCode : ℕ := 16

/-- SP1's `SyscallCode::COMMIT_DEFERRED_PROOFS`. -/
def commitDeferredCode : ℕ := 26

/-- SP1's `SyscallCode::HINT_LEN`. -/
def hintLenCode : ℕ := 240

/-- The bound both valid-field-element checks compare against: `0x7F00`, the second limb of
KoalaBear's modulus `p = 0x7F000001`. A word whose upper two limbs vanish and whose limb 1 is at
most this bound reduces to at most `p - 1`, so its single-cell reduction is injective — which is
what makes the committed exit code decode back to `a0` with no wraparound. -/
def fieldLimbBound : ℕ := 32512

/-- The `SyscallInstrs` row, grouped but in upstream column order (see the module docstring). -/
structure Inputs (F : Type) where
  state : CPUState F
  op_a : F
  op_a_memory : RegisterAccessCols F
  op_a_unchanged : F
  op_b : F
  op_b_memory : RegisterAccessCols F
  op_c : F
  op_c_memory : RegisterAccessCols F
  next_pc : Vector F 3
  is_halt : F
  op_a_value : Word F
  syscall_id_bytes : U16toU8Operation F
  is_enter_unconstrained : IsZeroOperation F
  is_hint_len : IsZeroOperation F
  is_halt_zero : IsZeroOperation F
  is_commit : IsZeroOperation F
  is_commit_deferred : IsZeroOperation F
  digest_index_bits : Vector F 8
  digest_word : Vector F 4
  op_b_cmp : U16CompareOperation F
  op_c_cmp : U16CompareOperation F
  is_real : F
deriving ProvableStruct

/-- The row is exactly as wide as the upstream table. This is the tripwire for the whole column
map: it fails if any field above is added, removed, reordered into a different size, or if an
upstream block changes shape. -/
theorem inputs_size : size Inputs = 65 := rfl

/-- The row's recombined 24-bit low clock, the standard `clk_0_16 + clk_16_24 · 2^16` spelling. -/
def clkLow (r : Inputs (ZMod p)) : ZMod p :=
  r.state.clk_0_16 + r.state.clk_16_24 * 65536

/-- **The exit-code word is a valid field element.** SP1's halt arm pins `a0`'s upper two limbs and
bounds limb 1 against `fieldLimbBound` (`U16CompareOperation` on `[16]` gated by `[31]`, then the
two conditionals `E88`/`E91`). Stated structurally, and therefore field-generically: the numeric
consequence — that the reduction `w0 + w1 · 2^16` is below the modulus and so decodes injectively —
needs KoalaBear's actual size and is derived where it is used, not asserted here.

This is what `HaltChip` omits. Pinning limb 1 to zero, as it does, is *strictly stronger* than SP1
and costs the profile every exit code above `2^16`. -/
def ExitCodeValid (w : Word (ZMod p)) : Prop :=
  w[2] = 0 ∧ w[3] = 0 ∧
    (w[1].val < fieldLimbBound ∨ (w[1].val = fieldLimbBound ∧ w[0] = 0))

/-- The syscall row's semantic contract.

Ungated: the two selector booleanities SP1 asserts unconditionally, the `CPUState` clock-byte
bounds at the syscall edge (`clk_inc = 264` — eight ticks for the instruction plus SP1's flat 256
per syscall), and the three register-access timestamp bounds at access clocks `+4`/`+3`/`+2` for
`t0`/`a0`/`a1`.

Gated on `is_halt` (which upstream already carries the `is_real` factor): the halt transition
parks the machine at `Machine.haltPc`, and the exit-code word is a valid field element.

The other four arms constrain columns this milestone leaves unconstrained; they are added with
their own conjuncts, and the anchor in `Faithful/SyscallChip.lean` is what will show the row is
complete against upstream. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.is_halt = 0 ∨ r.is_halt = 1) ∧
  Readers.CPUState.Spec
    { cols := r.state, next_pc := r.next_pc, clk_inc := 264, is_real := r.is_real } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_a_memory, is_real := r.is_real, clk_target := clkLow r + 4 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_b_memory, is_real := r.is_real, clk_target := clkLow r + 3 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_c_memory, is_real := r.is_real, clk_target := clkLow r + 2 } ∧
  (r.is_halt = 1 →
    r.next_pc = #v[1, 0, 0] ∧ ExitCodeValid r.op_b_memory.prev_value)

end SP1Clean.SyscallChip
