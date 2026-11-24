import SP1Clean.FormalModel.Contracts.WriteBuffer
import SP1Clean.Proofs.Operations.AddressDiv8
import SP1Clean.Proofs.Operations.AddrAddOperation.Address
import Clean.Gadgets.IsZeroField

/-! # Rounding a full byte endpoint to a 48-bit cell index

The low 48 bits are divided by eight. The fourth limb admits the one-past byte
address; at that endpoint every low limb is zero. Only the word index is added.
-/

namespace SP1Clean.WriteBuffer.Endpoint
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Low 48-bit portion supplied to the reusable division gadget. -/
def low {F : Type} [Zero F] (byte : Word F) : Word F := #v[byte[0], byte[1], byte[2], 0]

/-- Divide the low payload while retaining the original high byte-address limb. -/
def division {F : Type} [Zero F] (input : Endpoint F) : AddressDiv8.Inputs F := ⟨low input.byte, input.quotients⟩

/-- Include the endpoint's high bit and the nonempty partial word for ceiling division. -/
def adjustment {F : Type} [Zero F] [One F] [Sub F] [Mul F] [OfNat F 8192]
    (ceil : Bool) (top zero : F) : Word F := #v[if ceil then 1 - zero else 0, 0, top * 8192, 0]

/-- Enforce the high endpoint and use the bounded address adder on cell indices. -/
def main (ceil : Bool) (input : Var Endpoint (ZMod p)) : Circuit (ZMod p) Unit := do
  let div ← AddressDiv8.circuit (division input)
  let zero ← Gadgets.IsZeroField.circuit div.remainder
  let high := input.byte[3]
  assertBool high
  assertZero (high * input.byte[0])
  assertZero (high * input.byte[1])
  assertZero (high * input.byte[2])
  assertion AddrAddOperation.circuit ⟨Address.asWord div.quotient, adjustment ceil high zero, ⟨input.index⟩, 1⟩

instance elaborated (ceil : Bool) : ElaboratedCircuit (ZMod p) Endpoint unit (main ceil) := by elaborate_circuit

/-- Canonical natural endpoint and its exact requested cell. -/
def Spec (ceil : Bool) (input : Endpoint (ZMod p)) : Prop :=
  input.byte.isU64 ∧ input.byte.toNat ≤ 2 ^ 48 ∧ Address.Bounded input.index ∧
  Address.toNat input.index = cellIndex ceil input.byte.toNat

/-- The compiler calculates the division columns from public endpoint limbs. -/
def ProverAssumptions (ceil : Bool) (input : Endpoint (ZMod p)) : Prop :=
  Spec ceil input ∧ division input = AddressDiv8.populate (low input.byte)

/-- Build division and index witnesses for the chosen mathematical endpoint. -/
def populate (ceil : Bool) (byte : Word (ZMod p)) : Endpoint (ZMod p) :=
  ⟨byte, (AddressDiv8.populate (low byte)).quotients, Address.ofNat (cellIndex ceil byte.toNat)⟩

end SP1Clean.WriteBuffer.Endpoint
