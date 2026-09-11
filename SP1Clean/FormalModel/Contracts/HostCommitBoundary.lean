import SP1Clean.FormalModel.Contracts.HostCommit

/-! # Native commitment-bank endpoints

The bank starts with zero words at clock zero. A terminal row preserves its words and moves to
clock `2^48`, outside every ordinary bank row's bounded clock. The verifier can therefore bind
public final values without exposing the last commitment timestamp as a public field.
-/

namespace SP1Clean.HostCommitBoundary

open Circuit HostCommitChip

variable {p : ℕ} [Fact p.Prime]

def initial : State (ZMod p) := ⟨0, 0, Vector.replicate 8 0⟩

def final {R : Type} [OfNat R 16777216] [Zero R] (values : Vector (Word R) 8) : State R :=
  ⟨16777216, 0, values⟩

def TerminalSpec (input : State (ZMod p)) : Prop :=
  input.clk_high.val < 2 ^ 24 ∧ input.clk_low.val < 2 ^ 24

end SP1Clean.HostCommitBoundary
