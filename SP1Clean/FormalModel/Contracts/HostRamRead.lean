import SP1Clean.FormalModel.Contracts.HostRamAccess

/-! # A physical host RAM read

Each covered WRITE cell preserves its word, advances the physical Memory record once and
supplies one logical read. Buffer coverage and call identity are established by the consuming
tables, not by this provider's local contract. Released VERIFY makes no RAM requests.
-/

namespace SP1Clean.HostRamReadChip

open Circuit

structure Inputs (F : Type) where
  ram : HostRamAccessChip.Inputs F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

structure Message (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Message

def Message.address {R : Type} [Zero R] (message : Message R) : Word R :=
  #v[message.addr0, message.addr1, message.addr2, 0]

/-- Local shape of a read: one complete aligned guest cell and a canonical word.
The value's currency at the event clock is a separate Memory-grounding conclusion. -/
def Message.Valid {p : ℕ} [Fact p.Prime] (message : Message (ZMod p)) : Prop :=
  Word.isU64 message.address ∧ 2 ^ 16 ≤ Word.toNat message.address ∧
    Word.toNat message.address < 2 ^ 48 ∧ Word.toNat message.address % 8 = 0 ∧
    Word.isU64 message.value

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_ram_read"
  Guarantees message _ := message.Valid

def Inputs.message {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R]
    (input : Inputs R) : Message R :=
  ⟨input.ram.clk_high, input.ram.clockLow, input.ram.addr0, input.ram.addr1,
    input.ram.addr2, input.ram.new_value⟩

/-- One bounded, value-preserving transfer serving one consumer. -/
def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.Spec input.ram ∧
    input.ram.new_value = input.ram.access.prev_value

/-- All outgoing read guarantees follow from the physical access's local contract. -/
theorem Spec.message {p : ℕ} [Fact p.Prime] {input : Inputs (ZMod p)}
    (checked : Spec input) : input.message.Valid :=
  ⟨checked.1.1.2.1, checked.1.2.1.1, checked.1.2.1.2.1,
    checked.1.2.1.2.2, checked.1.2.2.2.1⟩

end SP1Clean.HostRamReadChip
