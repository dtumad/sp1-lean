import SP1Clean.Native.Operations.WriteCellEndpoint

/-! # Exact floor and ceiling cell indices at both ends of guest memory -/

namespace SP1Clean.WriteBuffer.Endpoint
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem split_word (b : Word (ZMod p)) :
    b.toNat = (low b).toNat + b[3].val * 2 ^ 48 := by simp [low, Word.toNat_def]

omit [Fact (2 ^ 17 < p)] in
private theorem bound_low {b : Word (ZMod p)} (valid : b.isU64) : (low b).isU64 := by
  apply Word.isU64_of_cases <;> simp only [low, circuit_norm, ZMod.val_zero] <;>
    first | exact valid 0 | exact valid 1 | exact valid 2 | norm_num

omit [Fact (2 ^ 17 < p)] in
private theorem low_lt {b : Word (ZMod p)} (valid : (low b).isU64) : (low b).toNat < 2 ^ 48 := by
  have bounds := Word.lt_cases_of_isU64 valid
  simp only [low, Word.toNat_def, circuit_norm, ZMod.val_zero] at *
  omega

omit [Fact (2 ^ 17 < p)] in
private theorem high_rule (b : Word (ZMod p)) (valid : (low b).isU64) :
    (IsBool b[3] ∧ b[3] * b[0] = 0 ∧ b[3] * b[1] = 0 ∧ b[3] * b[2] = 0) ↔
      b.isU64 ∧ b.toNat ≤ 2 ^ 48 := by
  have bounds := Word.lt_cases_of_isU64 valid
  simp only [low, circuit_norm] at bounds
  constructor
  · rintro ⟨bit, z0, z1, z2⟩
    rcases bit with h | h
    · rw [h, zero_mul] at z0 z1 z2
      constructor
      · apply Word.isU64_of_cases bounds.1 bounds.2.1 bounds.2.2.1
        simp [h]
      · rw [split_word, h, ZMod.val_zero, Nat.zero_mul, Nat.add_zero]
        exact (low_lt valid).le
    · simp only [h, one_mul] at z0 z1 z2
      constructor
      · apply Word.isU64_of_cases bounds.1 bounds.2.1 bounds.2.2.1
        simp [h, ZMod.val_one]
      · simp [Word.toNat_def, z0, z1, z2, h, ZMod.val_one]
  · rintro ⟨_, upper⟩
    simp only [Word.toNat_def] at upper
    by_cases absent : b[3] = 0
    · simp [absent, IsBool]
    · have positive : 0 < b[3].val := Nat.pos_of_ne_zero fun z => absent (ZMod.val_injective _ (by simpa only [ZMod.val_zero] using z))
      have one : b[3] = 1 := ZMod.val_injective _ (by rw [ZMod.val_one]; omega)
      have zi (x : ZMod p) (z : x.val = 0) : x = 0 := ZMod.val_injective _ (by simpa only [ZMod.val_zero] using z)
      simp only [one, IsBool, one_mul, or_true, true_and]
      exact ⟨zi _ (by omega), zi _ (by omega), zi _ (by omega)⟩

private theorem adjust_value (ceil : Bool) (top rem zero : ZMod p) (bit : IsBool top)
    (flag : zero = if rem = 0 then 1 else 0) :
    (adjustment ceil top zero).isU64 ∧ (adjustment ceil top zero).toNat =
      top.val * 2 ^ 45 + (if ceil = true ∧ rem ≠ 0 then 1 else 0) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have coeff : (8192 : ZMod p).val = 8192 := by
    simpa only [Nat.cast_ofNat] using (ZMod.val_natCast_of_lt (n := p) (a := 8192) (by omega))
  subst zero
  rcases bit with h | h <;> rw [h] <;> cases ceil <;> by_cases rz : rem = 0
  all_goals constructor
  all_goals first
    | apply Word.isU64_of_cases <;> simp [adjustment, rz, coeff, ZMod.val_one]
    | simp [adjustment, Word.toNat_def, rz, coeff, ZMod.val_one]

private theorem index_formula (ceil : Bool) (b : Word (ZMod p)) (d : AddressDiv8.Output (ZMod p))
    {q : fields 3 (ZMod p)} (division : AddressDiv8.Spec ⟨low b, q⟩ d) (z : ZMod p)
    (bit : IsBool b[3]) (flag : z = if d.remainder = 0 then 1 else 0) :
    (adjustment ceil b[3] z).isU64 ∧
    Word.toNat (Address.asWord d.quotient) + Word.toNat (adjustment ceil b[3] z) = cellIndex ceil b.toNat := by
  obtain ⟨bound, add⟩ := adjust_value ceil b[3] d.remainder z bit flag
  refine ⟨bound, ?_⟩
  rw [Address.toNat_asWord, division.2.2.2.1, add, split_word b]
  have rem := division.2.2.2.2.1
  have same : d.remainder = 0 ↔ (low b).toNat % 8 = 0 := by rw [← rem, ZMod.val_eq_zero]
  change (low b).toNat / 8 + _ = _
  cases ceil <;> by_cases zero : d.remainder = 0
  all_goals first | have _h := same.mp zero | have _h := same.not.mp zero
  all_goals simp [cellIndex, zero]; omega

private theorem holds (ceil : Bool) (i : Endpoint (ZMod p)) (d : AddressDiv8.Output (ZMod p))
    (div : AddressDiv8.Spec (division i) d) {z : ZMod p} (flag : z = if d.remainder = 0 then 1 else 0)
    (hi : IsBool i.byte[3] ∧ i.byte[3] * i.byte[0] = 0 ∧ i.byte[3] * i.byte[1] = 0 ∧ i.byte[3] * i.byte[2] = 0)
    (adder : AddrAddOperation.Assumptions ⟨Address.asWord d.quotient, adjustment ceil i.byte[3] z, ⟨i.index⟩, 1⟩ →
      AddrAddOperation.Spec ⟨Address.asWord d.quotient, adjustment ceil i.byte[3] z, ⟨i.index⟩, 1⟩) : Spec ceil i := by
  have canonical := (high_rule _ div.1).mp hi
  obtain ⟨adjusted, formula⟩ := index_formula ceil i.byte d div z hi.1 flag
  have capacity : cellIndex ceil i.byte.toNat < 2 ^ 48 := by
    have := canonical.2
    cases ceil <;> simp only [cellIndex, Bool.false_eq_true, ↓reduceIte] <;> omega
  have eq := AddrAddOperation.exact_sum _ _ _ (adder ⟨Address.isU64_asWord div.2.2.1, adjusted, Or.inr rfl⟩)
    (by rw [formula]; omega)
  exact ⟨canonical.1, canonical.2, eq.1, eq.2.1.trans formula⟩

private theorem checks (ceil : Bool) (i : Endpoint (ZMod p)) (d : AddressDiv8.Output (ZMod p))
    (div : AddressDiv8.Spec (division i) d) {z : ZMod p} (flag : z = if d.remainder = 0 then 1 else 0)
    (valid : Spec ceil i) :
    (IsBool i.byte[3] ∧ i.byte[3] * i.byte[0] = 0 ∧ i.byte[3] * i.byte[1] = 0 ∧ i.byte[3] * i.byte[2] = 0) ∧
    (AddrAddOperation.Assumptions ⟨Address.asWord d.quotient, adjustment ceil i.byte[3] z, ⟨i.index⟩, 1⟩ ∧
      AddrAddOperation.Spec ⟨Address.asWord d.quotient, adjustment ceil i.byte[3] z, ⟨i.index⟩, 1⟩) := by
  have hi := (high_rule _ div.1).mpr ⟨valid.1, valid.2.1⟩
  obtain ⟨adjusted, formula⟩ := index_formula ceil i.byte d div z hi.1 flag
  exact ⟨hi, ⟨Address.isU64_asWord div.2.2.1, adjusted, Or.inr rfl⟩,
    AddrAddOperation.spec_of_sum _ _ _ valid.2.2.1 (valid.2.2.2.trans formula.symm)⟩

omit [Fact (2 ^ 17 < p)] in
private theorem eval_div (env : Environment (ZMod p)) (i : Var Endpoint (ZMod p)) :
    ProvableStruct.eval env (division i) = division (ProvableStruct.eval env i) := by
  rcases i with ⟨_, _, _⟩
  simp only [division, low, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_adjust (env : Environment (ZMod p)) (ceil : Bool) (top z : Expression (ZMod p)) :
    Eval.eval env (adjustment ceil top z) = adjustment ceil (env top) (env z) := by
  cases ceil <;> simp only [adjustment, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (a : fields 3 (Expression (ZMod p))) :
    Eval.eval env (Address.asWord a) = Address.asWord (Eval.eval env a) := by simp only [Address.asWord, circuit_norm]

/-- Checked inclusive-domain endpoint division with selectable round direction. -/
def circuit (ceil : Bool) : GeneralFormalCircuit (ZMod p) Endpoint unit where
  main := main ceil
  elaborated := elaborated ceil
  computableWitnesses := by computable_witnesses [division, low, adjustment, Address.asWord]
  Spec input _ _ := Spec ceil input
  ProverAssumptions input _ _ := ProverAssumptions ceil input
  soundness := by
    circuit_proof_start [AddressDiv8.circuit, Gadgets.IsZeroField.circuit, AddrAddOperation.circuit,
      eval_div, eval_adjust, eval_asWord]
    obtain ⟨d, z, hi, z0, z1, z2, sum⟩ := h_holds
    exact holds ceil _ _ d z ⟨hi, z0, z1, z2⟩ sum
  completeness := by
    circuit_proof_start [AddressDiv8.circuit, Gadgets.IsZeroField.circuit, AddrAddOperation.circuit,
      eval_div, eval_adjust, eval_asWord]
    obtain ⟨valid, prepared⟩ := h_assumptions
    have bounded := bound_low valid.1
    have a : AddressDiv8.ProverAssumptions (division ⟨input_byte, input_quotients, input_index⟩) :=
      ⟨bounded, low_lt bounded, prepared⟩
    obtain ⟨d, z⟩ := h_env
    obtain ⟨⟨hi, z0, z1, z2⟩, sum⟩ := checks ceil _ _ (d a) z valid
    exact ⟨a, hi, z0, z1, z2, sum⟩

/-- The natural compiler supplies the entire local prover domain, including byte `2^48`. -/
theorem populate_valid (ceil : Bool) (byte : Word (ZMod p)) (valid : byte.isU64) (limit : byte.toNat ≤ 2 ^ 48) :
    ProverAssumptions ceil (populate ceil byte) := by
  have bound : cellIndex ceil byte.toNat < 2 ^ 48 := by
    cases ceil <;> simp only [cellIndex, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact ⟨⟨valid, limit, Address.bounded_ofNat _, Address.toNat_ofNat _ bound⟩, rfl⟩

end SP1Clean.WriteBuffer.Endpoint
