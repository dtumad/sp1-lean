import SP1Clean.Native.Operations.WriteProbe

/-! # Sound and complete read-only observation rows

The location check derives the register/RAM distinction from canonical key limbs.
Address and clock comparisons cannot alias through the coefficient field.
-/

namespace SP1Clean.WriteProbe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem upper_zero_iff {key : fields 3 (ZMod p)} (bounded : Address.Bounded key) :
    key[1] + key[2] = 0 ↔ Address.toNat key < 2 ^ 16 := by
  have lo := bounded 0
  have mid := bounded 1
  have high := bounded 2
  have primeBound := Fact.out (p := 2 ^ 17 < p)
  dsimp only [Address.toNat]
  change key[0].val < 2 ^ 16 at lo
  change key[1].val < 2 ^ 16 at mid
  change key[2].val < 2 ^ 16 at high
  have sum := ZMod.val_add_of_lt (a := key[1]) (b := key[2]) (by omega)
  constructor
  · intro eq
    rw [eq, ZMod.val_zero] at sum
    omega
  · intro small
    apply ZMod.val_injective p
    rw [ZMod.val_zero, sum]
    omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem low_key {key : fields 3 (ZMod p)} (small : Address.toNat key < 2 ^ 16) :
    Address.toNat key = key[0].val := by
  dsimp only [Address.toNat] at *
  omega

private theorem check_key {key : fields 3 (ZMod p)} {rem reg : ZMod p}
    (bounds : Address.Bounded key) (remainder : rem.val = Address.toNat key % 8)
    (tag : reg = if key[1] + key[2] = 0 then 1 else 0) :
    reg * (key[0] - 12) = 0 ∧ (1 - reg) * rem = 0 ↔ ValidKey (Address.toNat key) := by
  rw [tag]
  by_cases small : Address.toNat key < 2 ^ 16
  · have primeBound := Fact.out (p := 2 ^ 17 < p)
    have twelve : (12 : ZMod p).val = 12 := ZMod.val_natCast_of_lt (by omega : 12 < p)
    have low := low_key small
    rw [ite_eq_left ((upper_zero_iff bounds).mpr small)]
    simp only [one_mul, sub_eq_zero, sub_self, zero_mul, and_true, ValidKey]
    constructor
    · intro equal
      exact Or.inl (low.trans ((congrArg ZMod.val equal).trans twelve))
    · rintro (eq | ⟨impossible, _⟩)
      · exact ZMod.val_injective _ (by omega)
      · omega
  · have upper := Address.toNat_lt bounds
    rw [ite_eq_right (fun zero => small ((upper_zero_iff bounds).mp zero))]
    simp only [zero_mul, sub_zero, one_mul, true_and, ValidKey]
    constructor
    · rintro rfl
      exact Or.inr ⟨by omega, upper, by simpa using remainder.symm⟩
    · rintro (eq | ⟨_, _, aligned⟩)
      · omega
      · exact ZMod.val_injective _ (by simpa [remainder] using aligned)

omit [Fact (2 ^ 17 < p)] in
private theorem eval_division (env : Environment (ZMod p)) (x : Var Inputs (ZMod p)) :
    ProvableStruct.eval env x.division = (ProvableStruct.eval env x).division := by
  rcases x with ⟨⟨_, _, _, _⟩, _, _⟩
  simp only [Inputs.division, Address.asWord, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_asWord (env : Environment (ZMod p)) (x : fields 3 (Expression (ZMod p))) :
    Eval.eval env (Address.asWord x) = Address.asWord (Eval.eval env x) := by
  simp only [Address.asWord, circuit_norm]

/-- Checked read-only observation of an aligned RAM word or x12 at a bounded incoming clock. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_probe.row"
  main
  elaborated
  computableWitnesses := by computable_witnesses [Inputs.division, Address.asWord, Inputs.read]
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  channelsWithRequirements := [readChannel.toRaw]
  soundness := by
    circuit_proof_start [versionChannel, readChannel, AddressDiv8.circuit, Gadgets.IsZeroField.circuit,
      WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, AddressOrder.circuit,
      eval_division, eval_asWord]
    obtain ⟨div, tag, reg, ram, word, lower, clock, upper, lo, hi⟩ := h_holds
    have keyBound := Address.bounded_of_isU64_asWord div.1
    have lowBound := Address.bounded_of_isU64_asWord lower
    have clockBound := Address.bounded_of_isU64_asWord clock
    have highBound := Address.bounded_of_isU64_asWord upper
    have rem := div.2.2.2.2.1
    dsimp only [Inputs.division] at rem
    rw [Address.toNat_asWord] at rem
    exact ⟨keyBound, (check_key keyBound rem tag).mp ⟨reg, ram⟩, word, lowBound, clockBound, highBound,
      lo ⟨lowBound, clockBound⟩, hi ⟨clockBound, highBound⟩⟩
  completeness := by
    circuit_proof_start [versionChannel, readChannel, AddressDiv8.circuit, Gadgets.IsZeroField.circuit,
      WordRangeCheck.circuit, WordRangeCheck.Spec, WordRangeCheck.Assumptions, AddressOrder.circuit,
      eval_division, eval_asWord]
    obtain ⟨⟨keyBound, key, word, lo, clock, hi, first, last⟩, populated⟩ := h_assumptions
    have keyWord := Address.isU64_asWord keyBound
    have keyLt : Word.toNat (Address.asWord input_version_key) < 2 ^ 48 := by
      rw [Address.toNat_asWord]
      exact Address.toNat_lt keyBound
    have divAssumed := AddressDiv8.populate_assumptions _ keyWord keyLt
    rw [← populated] at divAssumed
    have div := h_env.1 divAssumed
    have rem := div.2.2.2.2.1
    dsimp only [Inputs.division] at rem
    rw [Address.toNat_asWord] at rem
    have checked := (check_key keyBound rem h_env.2).mpr key
    exact ⟨divAssumed, checked.1, checked.2, word, Address.isU64_asWord lo, Address.isU64_asWord clock,
      Address.isU64_asWord hi, ⟨⟨lo, clock⟩, first⟩, ⟨clock, hi⟩, last⟩

end SP1Clean.WriteProbe
