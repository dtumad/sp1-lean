import SP1Clean.FormalModel.Contracts.WriteProbe
import SP1Clean.Proofs.Operations.AddressDiv8
import SP1Clean.Native.Operations.AddressOrder
import SP1Clean.Native.Operations.WordRangeCheck

/-! # Native read-only WRITE probe row

The private version pull and the host-facing read receipt share the address and value.
All range and interval checks run on the same columns. The zero test distinguishes x12
from guest RAM by the upper two address limbs.
-/

namespace SP1Clean.WriteProbe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The original key undergoes one exact natural division by eight. -/
def Inputs.division {F : Type} [Zero F] (input : Inputs F) : AddressDiv8.Inputs F :=
  ⟨Address.asWord input.version.key, input.quotients⟩

/-- One genuine-version request and one host receipt. All comparison witnesses belong to
the Clean subcircuits. Sampling a word contributes zero SP1Memory traffic. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  versionChannel.pull input.version
  let div ← AddressDiv8.circuit input.division
  let reg ← Gadgets.IsZeroField.circuit (input.version.key[1] + input.version.key[2])
  assertZero (reg * (input.version.key[0] - 12))
  assertZero ((1 - reg) * div.remainder)
  assertion WordRangeCheck.circuit input.version.value
  assertion WordRangeCheck.circuit (Address.asWord input.version.lower)
  assertion WordRangeCheck.circuit (Address.asWord input.clock)
  assertion WordRangeCheck.circuit (Address.asWord input.version.upper)
  assertion AddressOrder.circuit ⟨input.version.lower, input.clock⟩
  assertion AddressOrder.circuit ⟨input.clock, input.version.upper⟩
  readChannel.push input.read

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by elaborate_circuit

/-- No external history predicate is a local prover input. -/
def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Spec input ∧ input.division = AddressDiv8.populate (Address.asWord input.version.key)

/-- Compute the private division columns from the genuine version and incoming clock. -/
def populate (version : Version (ZMod p)) (clock : fields 3 (ZMod p)) : Inputs (ZMod p) :=
  ⟨version, clock, (AddressDiv8.populate (Address.asWord version.key)).quotients⟩

end SP1Clean.WriteProbe
