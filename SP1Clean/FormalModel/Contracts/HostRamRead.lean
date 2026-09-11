import SP1Clean.FormalModel.Contracts.HostRamAccess
import Clean.Gadgets.Boolean

/-! # Sharing one physical host RAM read

WRITE requests each covered cell once. The two VERIFY_SP1_PROOF buffers can overlap and
request a cell twice. A read row preserves the word, advances its physical Memory record once,
and supplies one or two logical reads of that same word. Buffer coverage and call identity are
established by the consuming tables, not by this provider's local contract.
-/

namespace SP1Clean.HostRamReadChip

open Circuit

structure Inputs (F : Type) where
  ram : HostRamAccessChip.Inputs F
  shared : F
deriving ProvableStruct

structure Message (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F
deriving ProvableStruct

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_ram_read"
  Guarantees _ _ := True

def Inputs.message {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R]
    (input : Inputs R) : Message R :=
  ⟨input.ram.clk_high, input.ram.clockLow, input.ram.addr0, input.ram.addr1,
    input.ram.addr2, input.ram.new_value⟩

/-- One authentic, value-preserving transfer, serving one or two consumers. -/
def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.Spec input.ram ∧
    input.ram.new_value = input.ram.access.prev_value ∧ IsBool input.shared

end SP1Clean.HostRamReadChip
