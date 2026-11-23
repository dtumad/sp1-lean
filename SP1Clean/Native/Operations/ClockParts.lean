import SP1Clean.FormalModel.Contracts.ClockParts
import Clean.Gadgets.Bits

/-! # Checked decomposition of the complete State and Memory bus clock -/

namespace SP1Clean.ClockParts

open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Range-check the four pieces at the actual boundaries of the two encodings. -/
def main (c : Var ClockParts (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.low
  assertion (Gadgets.ToBits.rangeCheck 8 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.midLow
  assertion (Gadgets.ToBits.rangeCheck 8 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.midHigh
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.high

instance elaborated : ElaboratedCircuit (ZMod p) ClockParts unit main := by elaborate_circuit

/-- Enforce the common 16/8/8/16-bit decomposition before using either bus encoding. -/
def circuit : FormalAssertion (ZMod p) ClockParts where
  main
  elaborated
  Spec := Bounded
  soundness := by
    circuit_proof_start [Bounded, Gadgets.ToBits.rangeCheck]
    exact h_holds
  completeness := by
    circuit_proof_start [Bounded, Gadgets.ToBits.rangeCheck]
    exact h_spec

end SP1Clean.ClockParts
