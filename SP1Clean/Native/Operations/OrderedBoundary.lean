import SP1Clean.FormalModel.Contracts.OrderedBoundary
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal

/-! # A constrained ordered boundary link

Every row pulls its predecessor key and pushes its own key, both with unit multiplicity. Two
range checks and an unsigned comparison establish strict natural-number order. The channel
name is an ensemble parameter, allowing independent initialization and finalization chains.
-/

namespace SP1Clean.OrderedBoundary

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def channel (name : String) : Channel (ZMod p) Word where
  name
  Guarantees _ _ := True

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Spec input ∧ input.comparison = LtOperationUnsigned.populate input.previous input.current

def populate (previous current : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨previous, current, LtOperationUnsigned.populate previous current⟩

omit [Fact (2 ^ 17 < p)] in
theorem populate_assumptions (previous current : Word (ZMod p))
    (previousBound : Word.isU64 previous) (currentBound : Word.isU64 current)
    (increases : Word.toNat previous < Word.toNat current) :
    ProverAssumptions (populate previous current) :=
  ⟨⟨previousBound, currentBound, increases⟩, rfl⟩

def main (name : String) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit input.previous
  assertion WordRangeCheck.circuit input.current
  assertion LtOperationUnsigned.circuit ⟨input.previous, input.current, input.comparison, 1⟩
  assertZero (input.comparison.u16_compare_operation.bit - 1)
  (channel name).pull input.previous
  (channel name).push input.current

def circuit (name : String) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main name
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  channelsWithRequirements := [(channel name).toRaw]
  requirementsChannelsLawful := by
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
    · simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
    · intro env _
      simp only [main, circuit_norm, channel, WordRangeCheck.circuit]
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec, channel]
    obtain ⟨previousBound, currentBound, compare, one⟩ := h_holds
    have result := (LtOperationUnsigned.result_semantic previousBound currentBound rfl
      (compare ⟨fun _ => ⟨previousBound, currentBound⟩, Or.inr rfl⟩)).1
    change input_comparison_u16_compare_operation_bit =
      if Word.toNat input_previous < Word.toNat input_current then 1 else 0 at result
    rw [sub_eq_zero.mp one] at result
    refine ⟨previousBound, currentBound, ?_⟩
    split at result
    · assumption
    · exact False.elim (one_ne_zero result)
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec, ProverAssumptions, Spec, channel]
    obtain ⟨⟨previousBound, currentBound, increases⟩, comparisonEq⟩ := h_assumptions
    have compare := LtOperationUnsigned.spec_populate (b := input_previous) (cc := input_current)
    have result := (LtOperationUnsigned.result_semantic previousBound currentBound rfl compare).1
    rw [← comparisonEq] at compare result
    refine ⟨previousBound, currentBound,
      ⟨⟨fun _ => ⟨previousBound, currentBound⟩, Or.inr rfl⟩, compare⟩, ?_⟩
    dsimp only at result
    rw [result, if_pos increases, sub_self]

end SP1Clean.OrderedBoundary
