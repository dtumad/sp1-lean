import SP1Clean.Model.ByteProvider
import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import ToClean.Gadgets.OneHot
import ToClean.Gadgets.VariableRange

/-! # Prototype of a single provider for the complete SP1 byte bus

One circuit accepts all seven byte opcodes, including runtime range widths 0 through 16.
It shares byte decompositions across operations and proves exact preprocessed membership
even when the interaction count is zero. It is deliberately not installed in the machine's
physical inventory pending comparison with the existing six byte and seventeen range tables.
-/

namespace SP1Clean.ByteChip.Unified

open Circuit Utils.Bits Gadgets.BitwiseByte
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
private theorem opcode_bound : 7 ≤ p := by have := Fact.out (p := 2 ^ 17 < p); omega
omit [Fact p.Prime] in
private theorem range_bound : 2 ^ 16 < p := by have := Fact.out (p := 2 ^ 17 < p); omega

omit [Fact (2 ^ 17 < p)] in
private theorem msb_bit (b : F p) (hb : b.val < 2 ^ 8) :
    (fieldToBits 8 b)[7] = if 128 ≤ b.val then 1 else 0 := by
  rw [getElem_fieldToBits]
  simp only [Nat.shiftRight_eq_div_pow]
  have hd : b.val / 128 = if 128 ≤ b.val then 1 else 0 := by split <;> omega
  norm_num only [show (2 : ℕ) ^ 7 = 128 from by norm_num]
  rw [hd]
  split <;> norm_num

private theorem bitwise_spec (op : Op) {a b c : F p}
    (hb : b.val < 2 ^ 8) (hc : c.val < 2 ^ 8)
    (ha : a = (op.apply b.val c.val : F p)) :
    (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = op.apply b.val c.val := by
  have hlt := op.apply_lt hb hc
  rw [ha, ZMod.val_natCast_of_lt (lt_trans hlt two_pow_eight_lt)]
  exact ⟨⟨hlt, hb, hc⟩, rfl⟩

omit [Fact (2 ^ 17 < p)] in
private theorem bool_eq_ite {a : F p} {P : Prop} [Decidable P]
    (hbool : a = 0 ∨ a = 1) (hiff : a = 1 ↔ P) : a = if P then 1 else 0 := by
  split
  · exact hiff.mpr ‹P›
  · rcases hbool with h | h
    · exact h
    · exact False.elim (‹¬P› (hiff.mp h))

/-- A byte-bus key and its explicit LogUp multiplicity. -/
structure Inputs (F : Type) where
  /-- The complete opcode/result/operand key shared by both released tables. -/
  message : ByteRow F
  /-- The provider count; zero retains the occurrence and still requires valid membership. -/
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Check exact Byte/Range table membership and emit one counted provider occurrence. -/
def main (input : Var Inputs (F p)) : Circuit (F p) Unit := do
  let row := input.message
  let s ← Gadgets.OneHot.circuit 7 opcode_bound row.opcode
  let b ← Gadgets.ToBits.toBits 8 two_pow_eight_lt (((1 : Expression (F p)) - s[6]) * row.b)
  let c ← Gadgets.ToBits.toBits 8 two_pow_eight_lt (((1 : Expression (F p)) - s[6]) * row.c)
  assertZero (s[0] * (row.a - fieldFromBitsExpr (b.zipWith Op.and.bit c)))
  assertZero (s[1] * (row.a - fieldFromBitsExpr (b.zipWith Op.or.bit c)))
  assertZero (s[2] * (row.a - fieldFromBitsExpr (b.zipWith Op.xor.bit c)))
  assertZero (s[3] * row.a)
  assertZero (s[4] * row.a * (row.a - 1))
  assertion (Gadgets.ToBits.rangeCheck 8 two_pow_eight_lt)
    (s[4] * (row.b - row.c + row.a * 256))
  assertZero (s[5] * (row.a - b[7]))
  assertZero (s[5] * row.c)
  assertion (Gadgets.VariableRange.rangeCheck 16 range_bound) (s[6] * row.a, s[6] * row.b)
  assertZero (s[6] * row.c)
  byteChannel.pushIf input.multiplicity row

/-- Exact provider membership, without any condition on the interaction multiplicity. -/
def circuit : GeneralFormalCircuit (F p) Inputs unit where
  name := "sp1.prototype.byte"
  main
  Spec input _ _ := ByteProviderSpec input.message
  ProverAssumptions input _ _ := ByteProviderSpec input.message
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.OneHot.circuit, Gadgets.ToBits.toBits,
      Gadgets.ToBits.rangeCheck, Gadgets.VariableRange.rangeCheck]
    obtain ⟨⟨hop, hselectors⟩, ⟨hb, hbitsb⟩, ⟨hc, hbitsc⟩, hrest⟩ := h_holds
    have hs (i : ℕ) (hi : i < 7) : env.get (i₀ + i) =
        if input_message_opcode.val = i then 1 else 0 := by
      simpa only [circuit_norm] using congrArg (fun v : Vector (F p) 7 => v[i]) hselectors
    have hmsb := congrArg (fun v : Vector (F p) 8 => v[7]) hbitsb
    simp only [circuit_norm] at hmsb
    have hs0 := hs 0 (by decide)
    simp only [Nat.add_zero] at hs0
    simp only [fieldFromBits_eval, Vector.map_zipWith, Op.bit_eval, ← Vector.zipWith_map,
      hbitsb, hbitsc, hmsb] at hrest
    simp_rw [fieldFromBits_bitwise _ two_pow_eight_lt _ _ hb hc] at hrest
    simp only [hs0, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide),
      hs 4 (by decide), hs 5 (by decide), hs 6 (by decide)] at hb hc hrest
    have hspec : ByteProviderSpec
        ⟨input_message_opcode, input_message_a, input_message_b, input_message_c⟩ := by
      rw [byteProviderSpec_iff _ hop]
      interval_cases input_message_opcode.val <;>
        simp [ByteOpcode.constrain, sub_eq_zero] at hb hc hrest ⊢
      · exact bitwise_spec .and hb hc hrest
      · exact bitwise_spec .or hb hc hrest
      · exact bitwise_spec .xor hb hc hrest
      · simp [hrest, hb, hc]
      · exact ⟨⟨lt_trans (IsBool.val_lt_two hrest.1) (by decide), hb, hc⟩,
          hrest.1, Ltu.byte_ltu_iff hb hc hrest.1 hrest.2⟩
      · rw [hrest.1, msb_bit _ hb, hrest.2]
        by_cases h : 128 ≤ input_message_b.val <;> simp [h, hb, ZMod.val_one]
      · exact ⟨hrest.1.2, hrest.1.1, hrest.2⟩
    exact ⟨hspec, fun _ _ => hspec.byteRowSpec⟩
  completeness := by
    circuit_proof_start [Gadgets.OneHot.circuit, Gadgets.ToBits.toBits,
      Gadgets.ToBits.rangeCheck, Gadgets.VariableRange.rangeCheck]
    have hop := h_assumptions.opcode_lt
    obtain ⟨hselectors, hbitsb, hbitsc⟩ := h_env
    have hs (i : ℕ) (hi : i < 7) : env.get (i₀ + i) =
        if input_message_opcode.val = i then 1 else 0 := by
      simpa only [circuit_norm] using
        congrArg (fun v : Vector (F p) 7 => v[i]) (hselectors hop).2
    have hs0 := hs 0 (by decide)
    simp only [Nat.add_zero] at hs0
    rw [byteProviderSpec_iff _ hop] at h_assumptions
    have hbyte : input_message_opcode.val ≠ 6 →
        input_message_b.val < 256 ∧ input_message_c.val < 256 := by
      intro hne
      interval_cases input_message_opcode.val <;> simp_all [ByteOpcode.constrain]
    have hb : ((1 - env.get (i₀ + 6)) * input_message_b).val < 2 ^ 8 := by
      rw [hs 6 (by decide)]
      by_cases h : input_message_opcode.val = 6
      · simp [h]
      · simpa [h] using (hbyte h).1
    have hc : ((1 - env.get (i₀ + 6)) * input_message_c).val < 2 ^ 8 := by
      rw [hs 6 (by decide)]
      by_cases h : input_message_opcode.val = 6
      · simp [h]
      · simpa [h] using (hbyte h).2
    replace hbitsb := (hbitsb hb).2
    replace hbitsc := (hbitsc hc).2
    have hmsb := congrArg (fun v : Vector (F p) 8 => v[7]) hbitsb
    simp only [circuit_norm] at hmsb
    refine ⟨hop, hb, hc, ?_⟩
    simp only [fieldFromBits_eval, Vector.map_zipWith, Op.bit_eval, ← Vector.zipWith_map,
      hbitsb, hbitsc, hmsb]
    simp_rw [fieldFromBits_bitwise _ two_pow_eight_lt _ _ hb hc]
    simp only [hs0, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide),
      hs 4 (by decide), hs 5 (by decide), hs 6 (by decide)]
    interval_cases input_message_opcode.val <;>
      simp [ByteOpcode.constrain, sub_eq_zero, Op.apply] at h_assumptions ⊢
    · rw [← h_assumptions.2, ZMod.natCast_zmod_val]
    · rw [← h_assumptions.2, ZMod.natCast_zmod_val]
    · rw [← h_assumptions.2, ZMod.natCast_zmod_val]
    · exact h_assumptions.2
    · refine ⟨h_assumptions.2.1, ?_⟩
      rw [bool_eq_ite h_assumptions.2.1 h_assumptions.2.2]
      exact Ltu.byte_ltu_range h_assumptions.1.2.1 h_assumptions.1.2.2
    · exact ⟨(bool_eq_ite h_assumptions.1.2.1 h_assumptions.1.2.2).trans
        (msb_bit _ h_assumptions.1.1.2.1).symm, h_assumptions.2⟩
    · exact ⟨⟨h_assumptions.2.1, h_assumptions.1⟩, h_assumptions.2.2⟩

/-- The prototype checks membership with polynomial constraints only. -/
@[circuit_norm] theorem main_lookups (input : Var Inputs (F p)) (offset : ℕ) :
    ((main input).operations offset).lookups = [] := by
  simp [main, Gadgets.OneHot.circuit, Gadgets.OneHot.main, Gadgets.ToBits.toBits,
    Gadgets.ToBits.rangeCheck, Gadgets.VariableRange.rangeCheck, Gadgets.VariableRange.main,
    Gadgets.Equality.main, circuit_norm]

end SP1Clean.ByteChip.Unified
