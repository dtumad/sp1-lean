import SP1Clean.FormalModel.Contracts.WriteProbe

/-! # The clock-bound native WRITE packet passed from its ECALL to the word consumer -/

namespace SP1Clean.WritePacket

/-- Values consumed together by the buffer and host-effect verifier. -/
structure Header (F : Type) where
  /-- Incoming ECALL clock in three little-endian 16-bit limbs. -/
  clock : fields 3 F
  /-- x10, including the upper bits used by stdout and stderr dispatch. -/
  descriptor : Word F
  /-- x11 before the call. -/
  address : Word F
  /-- Complete x12 value supplied by the read-only observer. -/
  length : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Header

/-- Each active WRITE binds one complete packet to its instruction. -/
def channel {p : Nat} : Channel (ZMod p) Header where
  name := "sp1.native.write_packet"
  Guarantees _ _ := True

end SP1Clean.WritePacket
