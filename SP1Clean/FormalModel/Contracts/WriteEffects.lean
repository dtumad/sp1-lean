import SP1Clean.FormalModel.Contracts.WritePacketHeader

/-! # Private WRITE effect receipts

A classified header retains all original ECALL arguments, and each decoded word retains the
incoming clock, aligned guest address and all eight little-endian lanes. Even ignored writes
use the same pair of receipts.
-/

namespace SP1Clean.WriteEffects

/-- The result of dispatch stays attached to the original packet. -/
structure Request (F : Type) where
  /-- Incoming clock, descriptor, guest address and x12 byte count. -/
  header : WritePacket.Header F
  /-- Dispatch tag checked against the full descriptor. -/
  route : F
deriving ProvableStruct
provable_struct_eval_lemmas Request

/-- Private effect demand for one actual WRITE. -/
def requestChannel {p : Nat} : Channel (ZMod p) Request where
  name := "sp1.native.write_effect_request"
  Guarantees _ _ := True

/-- One complete decoded word ordered from the lowest to the highest byte. -/
structure Octets (F : Type) where
  /-- Aligned byte address of the source word. -/
  key : fields 3 F
  /-- Incoming ECALL clock shared by every byte of this word. -/
  clock : fields 3 F
  /-- Eight lanes in increasing guest-address order. -/
  bytes : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas Octets

/-- Private content demand for every actual aligned-word observation. -/
def octetsChannel {p : Nat} : Channel (ZMod p) Octets where
  name := "sp1.native.write_effect_octets"
  Guarantees _ _ := True

/-- Low-byte columns used by the ordinary SP1 safe byte decoder. -/
structure WordRow (F : Type) where
  /-- Original keyed word receipt before byte decomposition. -/
  read : WriteProbe.Read F
  /-- Low byte of each 16-bit input limb. -/
  low : Word F
deriving ProvableStruct
provable_struct_eval_lemmas WordRow

end SP1Clean.WriteEffects
