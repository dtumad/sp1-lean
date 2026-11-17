import SP1Clean.FormalModel.Contracts.OrdinaryObservation

/-! # Fixed endpoints of the ordinary observation chain

The chain starts at clock zero, below every ordinary source clock, with the incoming retirement
counter and nextPC. A terminal row moves the last observation to clock `2^48`, outside every
ordinary source clock, so a fixed verifier can bind the outgoing counter and nextPC without
exposing the last ordinary clock.

The terminal's mode records what the supplied target says about whether the segment retired an
ordinary instruction. That matters only when the target's retirement flag, interrupt refresh and
written event index differ between the two cases. The mode is static data of the target; the
terminal checks it against its own last observation.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- Seed the chain with the incoming counter and nextPC limbs, below every ordinary clock. -/
def start (counter : Word (ZMod p)) (pc : Vector (ZMod p) 3) : State (ZMod p) :=
  ⟨0, 0, counter, pc⟩

/-- The terminal's outgoing link, at clock `2^48`. -/
def final {R : Type} [OfNat R 16777216] [Zero R] (counter : Word R) (pc : Vector R 3) : State R :=
  ⟨16777216, 0, counter, pc⟩

/-- What the supplied target fixes about whether the segment observed an ordinary retirement. -/
inductive Mode
  /-- No ordinary instruction retired: the last observation is the start. -/
  | empty
  /-- At least one ordinary instruction retired: the last observation is a receipt. -/
  | nonempty
  /-- The target's bookkeeping is the same either way. -/
  | any
deriving DecidableEq

/-- The terminal's last observation has a bounded clock, consistent with the mode: the start's
clock is zero, and every observed receipt's is not. -/
def TerminalSpec (mode : Mode) (input : State (ZMod p)) : Prop :=
  input.clkHigh.val < 2 ^ 24 ∧ input.clkLow.val < 2 ^ 24 ∧
    match mode with
    | .empty => input.clkHigh = 0 ∧ input.clkLow = 0
    | .nonempty => ¬ (input.clkHigh = 0 ∧ input.clkLow = 0)
    | .any => True

end SP1Clean.OrdinaryObservation
