import SP1Clean.Proofs.Chips.HostNoopChip.Formal

/-! # One physical receipt for constrained ENTER and VERIFY

The code limb selects between the two constrained-replay contracts on an occupied row.
The enclosing guarded component controls physical demand padding.
-/

namespace SP1Clean.HostNoopChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Both full words have three zero upper limbs. The two low limbs determine the call and return. -/
def choiceMain (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let code := input.code[0]
  let result := input.result[0]
  assertZero ((code - 3) * (code - 27))
  assertZero ((code - 27) * result)
  assertZero ((code - 3) * (result - 27))
  assertZero input.code[1]
  assertZero input.code[2]
  assertZero input.code[3]
  assertZero input.result[1]
  assertZero input.result[2]
  assertZero input.result[3]
  HostCallChip.channel.pull input

instance choiceElaborated : ElaboratedCircuit (ZMod p) Inputs unit choiceMain := by elaborate_circuit

private theorem different : (3 : ZMod p) ≠ 27 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  intro same
  have eq := congrArg ZMod.val same
  change ((3 : ℕ) : ZMod p).val = ((27 : ℕ) : ZMod p).val at eq
  rw [ZMod.val_natCast_of_lt (by omega : 3 < p), ZMod.val_natCast_of_lt (by omega : 27 < p)] at eq
  contradiction

omit [Fact (2 ^ 17 < p)] in
private theorem word_eq (word : Word (ZMod p)) (low : ZMod p)
    (h0 : word[0] = low) (h1 : word[1] = 0) (h2 : word[2] = 0) (h3 : word[3] = 0) :
    word = #v[low, 0, 0, 0] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> assumption

/-- Formal soundness and completeness for the shared active HostCall receipt. -/
def choiceCircuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.enter_or_verify"
  main := choiceMain
  elaborated := choiceElaborated
  Spec input _ _ := ChoiceSpec input
  ProverAssumptions input _ _ := ChoiceSpec input
  channelsWithRequirements := [HostCallChip.channel.toRaw]
  soundness := by
    circuit_proof_start [choiceMain, Gadgets.Equality.circuit, HostCallChip.channel]
    obtain ⟨root, enterResult, verifyResult, c1, c2, c3, r1, r2, r3⟩ := h_holds
    simp only [mul_eq_zero, sub_eq_zero] at root enterResult verifyResult
    rcases root with enter | verify
    · left
      exact ⟨word_eq _ _ enter c1 c2 c3,
        word_eq _ _ (enterResult.resolve_left (enter ▸ different)) r1 r2 r3⟩
    · right
      exact ⟨word_eq _ _ verify c1 c2 c3,
        word_eq _ _ (verifyResult.resolve_left (verify ▸ Ne.symm different)) r1 r2 r3⟩
  completeness := by
    circuit_proof_start [choiceMain, Gadgets.Equality.circuit, HostCallChip.channel]
    rcases h_assumptions with ⟨code, result⟩ | ⟨code, result⟩ <;>
      dsimp only at code result <;>
      simp [code, result, codeWord, resultWord, circuit_norm]

end SP1Clean.HostNoopChip
