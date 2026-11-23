import SP1Clean.FormalModel.Contracts.WritePacketHeader

/-! # Private WRITE effect receipts

A classified header retains all original ECALL arguments, and each decoded word retains the
incoming clock, aligned guest address and all eight little-endian lanes. Even ignored writes
use the same pair of receipts.
-/

namespace SP1Clean.WriteEffects

/-- The result of dispatch stays attached to the original packet. -/
structure Request (F : Type) where
  header : WritePacket.Header F
  route : F
deriving ProvableStruct
provable_struct_eval_lemmas Request

/-- Private effect demand for one actual WRITE. -/
def requestChannel {p : Nat} : Channel (ZMod p) Request where
  name := "sp1.native.write_effect_request"
  Guarantees _ _ := True

/-- One complete decoded word ordered from the lowest to the highest byte. -/
structure Octets (F : Type) where
  key : fields 3 F
  clock : fields 3 F
  bytes : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas Octets

/-- Private content demand for every actual aligned-word observation. -/
def octetsChannel {p : Nat} : Channel (ZMod p) Octets where
  name := "sp1.native.write_effect_octets"
  Guarantees _ _ := True

/-- Low-byte columns used by the ordinary SP1 safe byte decoder. -/
structure WordRow (F : Type) where
  read : WriteProbe.Read F
  low : Word F
deriving ProvableStruct
provable_struct_eval_lemmas WordRow

end SP1Clean.WriteEffects
