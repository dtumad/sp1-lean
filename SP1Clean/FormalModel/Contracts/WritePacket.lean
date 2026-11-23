import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.ClockParts
import SP1Clean.FormalModel.Contracts.WritePacketHeader
import SP1Clean.Semantics.Transition.MicroTime

/-! # Binding the incoming WRITE clock to the native packet

One packet header carries the ECALL descriptor, buffer address and observed x12 length.
The standard four timestamp limbs determine both the released State clock and the native
observer clock. All word positions belonging to the packet use its incoming clock.
-/

namespace SP1Clean.WritePacket

/-- One outgoing packet and the timestamp parts shared by its incoming sources. -/
structure Inputs (F : Type) where
  /-- Canonical clock decomposition from the incoming CPU state. -/
  timestamp : ClockParts F
  /-- ECALL x10. -/
  descriptor : Word F
  /-- ECALL x11. -/
  address : Word F
  /-- Read-only x12 observation. -/
  length : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

section Messages

variable {R : Type} [Add R] [Mul R] [Zero R] [OfNat R 2] [OfNat R 12] [OfNat R 256] [OfNat R 65536]

/-- Both old and returned x5 carry the released WRITE code. -/
def Inputs.call (input : Inputs R) : HostCallChip.Message R :=
  ⟨input.timestamp.high24, input.timestamp.low24,
    #v[2, 0, 0, 0], input.descriptor, input.address, #v[2, 0, 0, 0]⟩

/-- Packet word queries use a single canonical 48-bit clock. -/
def Inputs.header (input : Inputs R) : Header R :=
  ⟨input.timestamp.address,
    input.descriptor, input.address, input.length⟩

/-- The packet length must come from the read receipt for register x12 at that same clock. -/
def Inputs.read (input : Inputs R) : WriteProbe.Read R :=
  ⟨#v[12, 0, 0], input.header.clock, input.length⟩

end Messages

/-- The two channel encodings refer to a single bounded incoming CPU clock. -/
def Spec {p : Nat} (input : Inputs (ZMod p)) : Prop :=
  input.timestamp.Bounded ∧
    Semantics.clkNat input.call.clk_high input.call.clk_low = Address.toNat input.read.clock

/-- A bounded timestamp identifies exactly one cut in both physical encodings. -/
theorem spec_of_bounded {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)] (input : Inputs (ZMod p))
    (bounds : input.timestamp.Bounded) : Spec input := ⟨bounds, (input.timestamp.time bounds).symm⟩

end SP1Clean.WritePacket
