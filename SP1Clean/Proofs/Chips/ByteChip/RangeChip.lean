import Clean.Air.WitnessGeneration.Generation
import ToClean.Gadgets.LookupProjection
import SP1Clean.Circuits.Channels.Channels
import SP1Clean.Circuits.Channels.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The in-circuit `RangeChip` provider (push side of SP1's variable-width range table)

SP1's `RangeChip` (`crates/core/machine/src/range/{air,columns}.rs`) is a **preprocessed** table over
all `(a, bits)` with `a < 2^bits`, `bits ≤ 16` (`RangePreprocessedCols { a, bits }`). Its AIR is a single
`receive_byte(ByteOpcode::Range(6), a, bits, 0, mult)` — on the Byte bus that *receive* is a **push** of
the valid range row `⟨6, a, bits, 0⟩`, balanced against the consumers' pulls. Several consumers
use fixed widths (notably 8, 13, 14, and 16), while ShiftLeft and ShiftRight can request widths
across the full `0, …, 16` interval. The native provider must therefore expose the complete
preprocessed family; four hand-picked tables leave valid shift rows without a native producer.

The installed providers prove each pushed row's `ByteRowSpec` membership in-circuit, using
`byteRowSpec_range`. Clean also supports verifier-fixed columns, as used by the native Program and
host-source providers. Moving this Range family to that representation requires migrating its
membership proofs and assembly together; the current bit-decomposition circuits remain the
production providers. Their message coverage matches SP1, but their physical layout and cost differ.

## Fixed-width family

SP1's preprocessed `bits` column enumerates the widths from zero through sixteen. Each
`circuitFor width` proves bit decomposition at that width and publishes exactly the rows
`⟨6, a, width, 0⟩` with `a < 2^width`. The verifier installs the fixed-width circuits in
the order `allWidths = List.finRange 17`.

Sibling: `Proofs/Chips/ByteChip/ByteChip.lean` (the `ByteChip` provider, opcodes 0..5 over `(b,c)`). -/

namespace SP1Clean.RangeChip

open Circuit
open SP1Clean (ByteRow ByteRowSpec)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `p > 2` (needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`), from `2^17 < p`. Kept **`local`** so
importing this provider (its wiring into `SP1Clean.lean`) does not leak a global `Fact (p > 2)` derived
from `Fact (2^17 < p)` — which would make downstream `omit [Fact (2^17 < p)]` clauses illegal (cf. the
`local instance : NeZero p` note in `Circuits/Channels/ByteTable.lean`). -/
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2^n < p` for any width `n ≤ 16` SP1's table uses (`bits ≤ 16`), from `2^17 < p`. -/
lemma two_pow_lt {n : ℕ} (h : n ≤ 16) : (2 : ℕ) ^ n < p := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have h1 : (2 : ℕ) ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- The committed value `a` — the `a` slot of SP1's `RangeChip` send `⟨6, a, bits, 0⟩`. The bit-width
`bits` is the compile-time parameter `n`. -/
structure Inputs (F : Type) where
  a : F
  /-- The LogUp count for this preprocessed range-table key. Zero is padding; larger values
  aggregate repeated occurrences. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Range-checks `a < 2^n` in-circuit (Clean `rangeCheck n` — a genuine bit decomposition, *not* a byte
lookup, so the provider owes nothing to the bus it provides), and pushes the `Range` row
`⟨6, a, (n : F), 0⟩` at the explicit input multiplicity. -/
def main (n : ℕ) (hn : 2 ^ n < p) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck n hn) input.a
  byteChannel.pushIf input.multiplicity
    (⟨6, input.a, Expression.const ((n : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))

/-- A width supported by SP1's preprocessed range table: exactly `0, …, 16`. -/
abbrev Width := Fin 17

/-- The canonical increasing order of all fixed-width provider tables. -/
def allWidths : List Width := List.finRange 17

/-- The native provider associated with this width in the released preprocessed Range table. -/
def circuitFor (width : Width) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := s!"sp1.native.range.{width.val}"
  main := main width.val (two_pow_lt (Nat.le_of_lt_succ width.isLt))
  Spec input _ _ := input.a.val < 2 ^ width.val
  ProverAssumptions input _ _ := input.a.val < 2 ^ width.val
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact ⟨h_holds,fun _ => (byteRowSpec_range input_a (Nat.le_of_lt_succ width.isLt)).mpr h_holds⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck]
    exact h_assumptions

omit [Fact (2 ^ 17 < p)] in
/-- Every supported width uses bit constraints, with no static lookup dependency. -/
@[circuit_norm] theorem main_lookups (n : ℕ) (bound : 2 ^ n < p)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main n bound input).operations offset).lookups = [] := by
  simp [main, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]

/-- Route the Range opcode by its declared width and count repeated full messages. -/
def generation (width : ℕ) : Air.Flat.WitnessGeneration.Generation (ZMod p) Inputs :=
  .demand {
    channel := byteChannel
    trigger := .pull
    guard message := .and (.feq (.expr message.opcode) (.const 6))
      (.feq (.expr message.b) (.const (width : ZMod p)))
    input message := pure ⟨message.a, .multiplicity⟩
  }

end SP1Clean.RangeChip
