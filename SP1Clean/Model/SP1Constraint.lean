module

public import Mathlib.Data.ZMod.Basic
public import SP1Clean.Math.Bitwise

/-! # SP1 byte-channel opcodes and their semantic predicates

The seven opcode tags follow released SP1's Byte table. Their predicates describe bounded
byte arithmetic and range membership independently of circuit implementations. Raw field
opcodes use an explicit tag witness, so out-of-range values cannot alias the enum decoder.
-/

@[expose] public section

namespace SP1Clean

variable {p : ℕ}

/-! ## Byte operations -/

inductive ByteOpcode | AND | OR | XOR | U8Range | LTU | MSB | Range
  deriving DecidableEq

namespace ByteOpcode

/-! Lean auto-generates `ByteOpcode.ofNat : ℕ → ByteOpcode` for this enum, mapping by
constructor index — AND=0, OR=1, XOR=2, U8Range=3, LTU=4, MSB=5, Range=6 — which is exactly
SP1's `ByteOpcode` numbering. The `@[simp]` lemmas below fix each valid decoding case. -/

@[simp] lemma ofNat_zero  : ofNat 0 = .AND := rfl
@[simp] lemma ofNat_one   : ofNat 1 = .OR  := rfl
@[simp] lemma ofNat_two   : ofNat 2 = .XOR := rfl
@[simp] lemma ofNat_three : ofNat 3 = .U8Range := rfl
@[simp] lemma ofNat_four  : ofNat 4 = .LTU := rfl
@[simp] lemma ofNat_five  : ofNat 5 = .MSB := rfl
@[simp] lemma ofNat_six   : ofNat 6 = .Range := rfl

/-- The opcode's table index as a `ℕ` — the inverse of the auto-generated `ofNat`
(AND=0, OR=1, XOR=2, U8Range=3, LTU=4, MSB=5, Range=6), matching SP1's byte-bus numbering. -/
def idx : ByteOpcode → ℕ
  | AND => 0
  | OR => 1
  | XOR => 2
  | U8Range => 3
  | LTU => 4
  | MSB => 5
  | Range => 6

@[simp] lemma ofNat_idx (op : ByteOpcode) : ofNat op.idx = op := by cases op <;> rfl

/-- The byte-opcode constraint. `Range` (used by Add's `slice_range_check_u16`) bounds
`a.val < 2 ^ b.val`; `U8Range` (used by CPUState's `clk_16_24` byte check) bounds all three
operands `< 256`; AND/OR/XOR (used by Bitwise) say `a` is the per-byte bitwise op of the
two byte operands, all bounded `< 256`; `MSB` (used by Mul/LoadByte/signed-Lt) says `a` is the
boolean top bit of `b` (`a = 1 ↔ 128 ≤ b.val`); `LTU` says `a` is the boolean `b.val < c.val`. -/
def constrain {p : ℕ} [NeZero p] (op : ByteOpcode) (a b c : ZMod p) : Prop :=
  match op with
  | AND => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val &&& c.val
  | OR  => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val ||| c.val
  | XOR => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val ^^^ c.val
  | U8Range => a.val < 256 ∧ b.val < 256 ∧ c.val < 256
  | LTU => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b.val < c.val)
  | MSB => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ 128 ≤ b.val)
  | Range => a.val < 2 ^ b.val

/-- Meaning of a raw field-valued byte-bus opcode. This is the form carried by SP1's AIR
interaction tuple: a valid byte row must exhibit an actual `ByteOpcode` whose numeric index is the
raw opcode field. Keeping this relation separate from `ByteOpcode.ofNat` is essential because the
generated enum decoder maps every out-of-range natural to `.Range`. -/
def constrainField {p : ℕ} [NeZero p] (opcode a b c : ZMod p) : Prop :=
  ∃ op : ByteOpcode, ((op.idx : ℕ) : ZMod p) = opcode ∧ op.constrain a b c

/-- Decode a raw byte opcode known to be one of the seven table indices. The large-field
hypothesis makes the numeric opcode casts injective; all SP1 chip theorems use the stronger
standard assumption `2^17 < p`. -/
lemma constrainField_natCast {p k : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (hk : k ≤ 6) (a b c : ZMod p) :
    constrainField ((k : ℕ) : ZMod p) a b c ↔ (ofNat k).constrain a b c := by
  have hp : 2 ^ 17 < p := Fact.out
  constructor
  · rintro ⟨op, hop, hc⟩
    have hopLt : op.idx < p := by cases op <;> simp only [idx] <;> omega
    have hkLt : k < p := by omega
    have hidx : op.idx = k := by
      have hval := congrArg ZMod.val hop
      rwa [ZMod.val_natCast_of_lt hopLt, ZMod.val_natCast_of_lt hkLt] at hval
    rwa [← hidx, ofNat_idx]
  · intro hc
    have hidx : (ofNat k).idx = k := by interval_cases k <;> rfl
    exact ⟨ofNat k, by rw [hidx], hc⟩

@[simp] lemma constrainField_zero {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (0 : ZMod p) a b c ↔ AND.constrain a b c := by
  simpa only [Nat.cast_zero, ofNat_zero] using
    constrainField_natCast (p := p) (k := 0) (by omega) a b c

@[simp] lemma constrainField_one {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (1 : ZMod p) a b c ↔ OR.constrain a b c := by
  simpa only [Nat.cast_one, ofNat_one] using
    constrainField_natCast (p := p) (k := 1) (by omega) a b c

@[simp] lemma constrainField_two {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (2 : ZMod p) a b c ↔ XOR.constrain a b c :=
  constrainField_natCast (k := 2) (by omega) a b c

@[simp] lemma constrainField_three {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (3 : ZMod p) a b c ↔ U8Range.constrain a b c :=
  constrainField_natCast (k := 3) (by omega) a b c

@[simp] lemma constrainField_four {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (4 : ZMod p) a b c ↔ LTU.constrain a b c :=
  constrainField_natCast (k := 4) (by omega) a b c

@[simp] lemma constrainField_five {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (5 : ZMod p) a b c ↔ MSB.constrain a b c :=
  constrainField_natCast (k := 5) (by omega) a b c

@[simp] lemma constrainField_six {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b c : ZMod p) :
    constrainField (6 : ZMod p) a b c ↔ Range.constrain a b c :=
  constrainField_natCast (k := 6) (by omega) a b c

@[simp] lemma constrain_Range {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.Range.constrain a b c ↔ (a.val < 2 ^ b.val) := Iff.rfl

@[simp] lemma constrain_U8Range {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.U8Range.constrain a b c ↔ (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) := Iff.rfl

@[simp] lemma constrain_LTU {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.LTU.constrain a b c ↔
      ((a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b.val < c.val)) :=
  Iff.rfl

@[simp] lemma constrain_MSB {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.MSB.constrain a b c ↔
      ((a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ 128 ≤ b.val)) :=
  Iff.rfl

end ByteOpcode

end SP1Clean
