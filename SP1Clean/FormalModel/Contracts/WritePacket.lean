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

/-- Build the packet input from the instruction receipt and the word returned for x12. -/
def populate {p : Nat} [Fact p.Prime] (call : HostCallChip.Message (ZMod p)) (length : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨ClockParts.split call.clk_high call.clk_low, call.arg1, call.arg2, length⟩

/-- Constructor completeness includes exact agreement with the complete instruction message. -/
theorem populate_write {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)] (call : HostCallChip.Message (ZMod p))
    (length : Word (ZMod p)) (high : call.clk_high.val < 2 ^ 24) (low : call.clk_low.val < 2 ^ 24)
    (code : call.code = #v[2, 0, 0, 0]) (returns : call.result = call.code) :
    let input := populate call length
    input.timestamp.Bounded ∧ input.call = call ∧
      Address.toNat input.read.clock = Semantics.clkNat call.clk_high call.clk_low ∧ input.read.value = length := by
  obtain ⟨bounded, hi, lo⟩ := ClockParts.split_spec call.clk_high call.clk_low high low
  refine ⟨bounded, ?_, ?_, rfl⟩
  · cases call
    simp only [populate, Inputs.call] at *
    rw [hi, lo, ← code, returns]
  · exact ((ClockParts.split call.clk_high call.clk_low).time bounded).trans (congrArg₂ Semantics.clkNat hi lo)

end SP1Clean.WritePacket
