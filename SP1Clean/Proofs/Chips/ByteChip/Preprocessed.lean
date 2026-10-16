module

public import SP1Clean.Model.ByteProvider
public import SP1Clean.Model.Channels
public import ToClean.Air.FixedPrefix

/-! # SP1-shaped preprocessed Byte and Range providers

This experiment retains the released physical rows, including repeated MSB keys and both
zero-width range rows. Fixed columns establish membership; only multiplicities are committed.
It is not installed in the machine inventory.
-/

@[expose] public section

namespace SP1Clean.ByteChip.Preprocessed

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local notation "Fp" => ZMod p
/-- Seven fixed byte values followed by six independent counts. -/
abbrev ByteInput := ProvablePair (fields 7) (fields 6)
/-- Fixed range value and width followed by their count. -/
abbrev RangeInput := ProvablePair (fields 2) field

/-- SP1's fixed columns in source order: b, c, AND, OR, XOR, LTU, MSB. -/
def byteValues (b c : ℕ) : Vector Fp 7 :=
  #v[b, c, b &&& c, b ||| c, b ^^^ c, if b < c then 1 else 0,
    if 128 ≤ b then 1 else 0]

/-- All six Byte interactions, retaining the MSB key's fixed zero third operand. -/
def byteMessages {F : Type} [OfNat F 0] [OfNat F 1] [OfNat F 2] [OfNat F 3]
    [OfNat F 4] [OfNat F 5] (row : Vector F 7) : Vector (ByteRow F) 6 :=
  #v[⟨0, row[2], row[0], row[1]⟩, ⟨1, row[3], row[0], row[1]⟩,
     ⟨2, row[4], row[0], row[1]⟩, ⟨3, 0, row[0], row[1]⟩,
     ⟨4, row[5], row[0], row[1]⟩, ⟨5, row[6], row[0], 0⟩]

/-- Every fixed byte message has the exact semantic meaning, independently of its count. -/
theorem byteValues_spec {b c : ℕ} (hb : b < 256) (hc : c < 256) (op : Fin 6) :
    ByteProviderSpec ((byteMessages (byteValues (p := p) b c))[op]) := by
  have hp : 256 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  let : Fact (1 < p) := ⟨by omega⟩
  have hbval := ZMod.val_natCast_of_lt (n := p) (lt_trans hb hp)
  have hcval := ZMod.val_natCast_of_lt (n := p) (lt_trans hc hp)
  have hand : b &&& c < 256 := Nat.and_lt_two_pow (n := 8) b hc
  have hor : b ||| c < 256 := Nat.or_lt_two_pow (n := 8) hb hc
  have hxor : b ^^^ c < 256 := Nat.xor_lt_two_pow (n := 8) hb hc
  fin_cases op <;>
    simp only [byteMessages, byteValues, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ByteProviderSpec, ByteRowSpec] <;>
    simp [ByteOpcode.constrain, hbval, hcval, hb, hc, ZMod.val_one,
      ZMod.val_natCast_of_lt (lt_trans hand hp),
      ZMod.val_natCast_of_lt (lt_trans hor hp),
      ZMod.val_natCast_of_lt (lt_trans hxor hp)] <;>
    (try split_ifs) <;> simp_all [ZMod.val_one, ZMod.val_zero]

/-- The verifier's seven byte columns, computed from the physical row index. -/
def byteFixed : FixedColumns Fp where
  height := 65536
  program :=
    let b : Witgen.U64Expr Fp := .div .idx (.const 256)
    let c : Witgen.U64Expr Fp := .mod .idx (.const 256)
    .ofFExprs #v[.ofU64 b, .ofU64 c, .ofU64 (.land b c), .ofU64 (.lor b c),
      .ofU64 (.lxor b c), .ite (.lt b c) (.const 1) (.const 0),
      .ite (.lt b (.const 128)) (.const 0) (.const 1)]
  valid := by rfl

omit [Fact (2 ^ 17 < p)] in
/-- The exported row formula agrees with the mathematical byte-pair enumeration. -/
theorem byteFixed_row {i : ℕ} (bound : i < 65536) :
    (byteFixed (p := p)).row (UInt64.ofNat i) = (byteValues (i / 256) (i % 256)).toArray := by
  have hi : i < UInt64.size := by change i < 18446744073709551616; omega
  simp [FixedColumns.row, byteFixed, Witgen.RowProgram.ofFExprs, Witgen.RowProgram.eval,
    Witgen.evalSteps, Witgen.VExpr.eval, Witgen.FExpr.eval, Witgen.U64Expr.eval,
    Witgen.BExpr.eval, byteValues, UInt64.toNat_ofNat_of_lt' hi, UInt64.toNat_div,
    UInt64.toNat_mod, UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_xor,
    UInt64.lt_iff_toNat_lt]
  split_ifs <;> first | rfl | omega

/-- A row emits the six SP1 Byte messages using its six independent multiplicities. -/
def byteCircuit : GeneralFormalCircuit Fp ByteInput unit where
  name := "sp1.prototype.fixed-byte"
  main input := do
    let messages := byteMessages input.1
    forEach (Vector.finRange 6) fun i => do
      Channels.byteChannel.emit input.2[i] messages[i]
  Assumptions input _ := ∀ i : Fin 6, ByteProviderSpec (byteMessages input.1)[i]
  Spec input _ _ := ∀ i : Fin 6, ByteProviderSpec (byteMessages input.1)[i]
  channelsWithRequirements := [Channels.byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Channels.byteChannel]
    refine ⟨h_assumptions, ?_⟩
    intro i _ _
    subst input
    have valid := (h_assumptions i).byteRowSpec
    fin_cases i <;> simpa [byteMessages, circuit_norm] using valid
  completeness := by circuit_proof_start [Channels.byteChannel]

/-- Fixed preprocessing discharges all provider validity assumptions. -/
def byteComponent : Component Fp where
  circuit := byteCircuit
  fixedColumns := some byteFixed
  Assumptions _ _ := True
  circuit_assumptions_of_assumptions := by
    intro i input data fixed _ _
    have fixedCells := FixedInputAt.input_prefix (input := input)
      (show (byteFixed (p := p)).width = size (fields 7) from rfl) fixed
    have height : i.toNat < 65536 := (fixed _ rfl).1
    have rowEq := byteFixed_row (p := p) height
    simp only [UInt64.ofNat_toNat] at rowEq
    rw [rowEq] at fixedCells
    have decoded : input.1 = byteValues (i.toNat / 256) (i.toNat % 256) :=
      Vector.toArray_inj.mp fixedCells
    change ∀ op : Fin 6, ByteProviderSpec (byteMessages input.1)[op]
    rw [decoded]
    exact byteValues_spec (by omega) (Nat.mod_lt _ (by decide))
  fixed_width_le_input := by change 7 ≤ 13; decide

/-- The range width at a physical index; index zero is the extra zero row. -/
def rangeBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i => if i < 2 ^ (n + 1) then rangeBits n i else n + 1

/-- The bounded decision tree never exceeds its configured width. -/
theorem rangeBits_le (n i : ℕ) : rangeBits n i ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rangeBits]; split <;> omega

/-- A bounded decision tree in Clean's existing witness IR, with no literal row table. -/
def rangeBitsIR {F : Type} : ℕ → Witgen.U64Expr F
  | 0 => .const 0
  | n + 1 => .ite (.lt .idx (.const (UInt64.ofNat (2 ^ (n + 1)))))
      (rangeBitsIR n) (.const (UInt64.ofNat (n + 1)))

/-- Range preprocessing reads only its public row index. -/
theorem rangeBitsIR_valid {F : Type} (n : ℕ) :
    (rangeBitsIR (F := F) n).validForRow .fixed = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rangeBitsIR, Witgen.U64Expr.validForRow, Witgen.BExpr.validForRow] using ih

omit [Fact (2 ^ 17 < p)] in
/-- The witness IR implements the same bounded width search. -/
theorem rangeBitsIR_eval (ctx : Witgen.Ctx Fp) (n : ℕ) (hn : n ≤ 16)
    (hi : ctx.idx < 131072) :
    ((rangeBitsIR n).eval ctx).toNat = rangeBits n ctx.idx := by
  have hi64 : ctx.idx < UInt64.size := by change ctx.idx < 18446744073709551616; omega
  induction n with
  | zero => rfl
  | succ n ih =>
    have power : 2 ^ (n + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hn
    have power64 : 2 ^ (n + 1) < UInt64.size := by
      change 2 ^ (n + 1) < 18446744073709551616; omega
    have n64 : n + 1 < UInt64.size := by change n + 1 < 18446744073709551616; omega
    simp only [rangeBitsIR, Witgen.U64Expr.eval, Witgen.BExpr.eval,
      UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hi64,
      UInt64.toNat_ofNat_of_lt' power64, rangeBits]
    split <;> rename_i h <;> simp only [decide_eq_true_eq] at h
    · simpa [h] using ih (by omega)
    · simp [h]

/-- Verifier-owned `(a,bits)` columns, in SP1's exact physical order. -/
def rangeFixed : FixedColumns Fp where
  height := 131072
  program := {
    width := 2
    steps := [.letU (rangeBitsIR 16)]
    output := .lit #v[.ofU64 (.mod .idx (.pow2 (.localVar 0))), .ofU64 (.localVar 0)]
  }
  valid := by simp [Witgen.RowProgram.Valid, Witgen.Step.validForRow,
    rangeBitsIR_valid, Witgen.VExpr.validForRow, Witgen.FExpr.validForRow,
    Witgen.U64Expr.validForRow]

omit [Fact (2 ^ 17 < p)] in
/-- The compact range initializer reproduces SP1's enumeration, including row zero. -/
theorem rangeFixed_row {i : ℕ} (bound : i < 131072) :
    (rangeFixed (p := p)).row (UInt64.ofNat i) =
      #[((i % 2 ^ rangeBits 16 i : ℕ) : Fp), ((rangeBits 16 i : ℕ) : Fp)] := by
  have hi64 : i < UInt64.size := by change i < 18446744073709551616; omega
  have bits := rangeBits_le 16 i
  have power : 2 ^ rangeBits 16 i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) bits
  simp [FixedColumns.row, rangeFixed, Witgen.RowProgram.eval, Witgen.evalSteps,
    Witgen.VExpr.eval, Witgen.FExpr.eval, Witgen.U64Expr.eval,
    UInt64.toNat_ofNat_of_lt' hi64, UInt64.toNat_mod, UInt64.toNat_shiftLeft,
    rangeBitsIR_eval, bound, Nat.shiftLeft_eq, Nat.mod_eq_of_lt,
    show rangeBits 16 i < 64 by omega,
    show 2 ^ rangeBits 16 i < 18446744073709551616 by omega]

/-- The range interaction is the same four-field message used by byte operations. -/
def rangeMessage {F : Type} [OfNat F 6] [OfNat F 0] (row : Vector F 2) : ByteRow F :=
  ⟨6, row[0], row[1], 0⟩

/-- Every bounded range pair satisfies exact provider membership. -/
theorem rangeValues_spec {a bits : ℕ} (ha : a < 2 ^ bits) (hb : bits ≤ 16) :
    ByteProviderSpec (rangeMessage (#v[(a : Fp), (bits : Fp)])) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have power : 2 ^ bits ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hb
  have hap : a < p := by omega
  have hbp : bits < p := by omega
  have member := (byteRowSpec_range (a : Fp) hbp).mpr (by
    simpa only [ZMod.val_natCast_of_lt hap] using ha)
  refine ⟨member, ?_, ?_, ?_⟩ <;>
    simp [rangeMessage, ZMod.val_natCast_of_lt hbp, hb]

/-- The Range AIR has one count column and no membership constraints. -/
def rangeCircuit : GeneralFormalCircuit Fp RangeInput unit where
  name := "sp1.prototype.fixed-range"
  main input := Channels.byteChannel.emit input.2 (rangeMessage input.1)
  Assumptions input _ := ByteProviderSpec (rangeMessage input.1)
  Spec input _ _ := ByteProviderSpec (rangeMessage input.1)
  channelsWithRequirements := [Channels.byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Channels.byteChannel, rangeMessage]
    subst input
    refine ⟨h_assumptions, fun _ _ => ?_⟩
    simpa only [Vector.getElem_map] using h_assumptions.byteRowSpec
  completeness := by circuit_proof_start [Channels.byteChannel, rangeMessage]

/-- Fixed range membership applies even to inactive rows and both repeated zero keys. -/
def rangeComponent : Component Fp where
  circuit := rangeCircuit
  fixedColumns := some rangeFixed
  Assumptions _ _ := True
  circuit_assumptions_of_assumptions := by
    intro i input data fixed _ _
    have fixedCells := FixedInputAt.input_prefix (input := input)
      (show (rangeFixed (p := p)).width = size (fields 2) from rfl) fixed
    have height : i.toNat < 131072 := (fixed _ rfl).1
    have rowEq := rangeFixed_row (p := p) height
    simp only [UInt64.ofNat_toNat] at rowEq
    rw [rowEq] at fixedCells
    have decoded : input.1 = #v[((i.toNat % 2 ^ rangeBits 16 i.toNat : ℕ) : Fp),
        ((rangeBits 16 i.toNat : ℕ) : Fp)] := Vector.toArray_inj.mp fixedCells
    change ByteProviderSpec (rangeMessage input.1)
    rw [decoded]
    exact rangeValues_spec (Nat.mod_lt _ (by positivity)) (rangeBits_le 16 i.toNat)
  fixed_width_le_input := by change 2 ≤ 3; decide

/-- SP1's honest index for a range key, including index one for the zero-width key. -/
theorem rangeBits_index {n bits a : ℕ} (hb : bits ≤ n) (ha : a < 2 ^ bits) :
    rangeBits n (2 ^ bits + a) = bits := by
  induction n with
  | zero => simp [rangeBits, show bits = 0 by omega]
  | succ n ih =>
    simp only [rangeBits]
    by_cases equal : bits = n + 1
    · subst bits
      rw [if_neg (by omega)]
    · have le : bits ≤ n := by omega
      have power : 2 ^ bits ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) le
      rw [if_pos (by rw [pow_succ]; omega)]
      exact ih le

omit [Fact (2 ^ 17 < p)] in
/-- Every valid range member occurs at the canonical physical index. -/
theorem rangeFixed_coverage {a bits : ℕ} (ha : a < 2 ^ bits) (hb : bits ≤ 16) :
    (rangeFixed (p := p)).row (UInt64.ofNat (2 ^ bits + a)) = #[(a : Fp), (bits : Fp)] := by
  have power : 2 ^ bits ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hb
  rw [rangeFixed_row (by omega), rangeBits_index hb ha]
  simp [Nat.mod_eq_of_lt ha]

omit [Fact (2 ^ 17 < p)] in
/-- Every byte pair occurs at SP1's canonical index (MSB uses `c = 0`). -/
theorem byteFixed_coverage {b c : ℕ} (hb : b < 256) (hc : c < 256) :
    (byteFixed (p := p)).row (UInt64.ofNat (256 * b + c)) = (byteValues b c).toArray := by
  rw [byteFixed_row (by omega)]
  congr 2 <;> omega

end SP1Clean.ByteChip.Preprocessed
