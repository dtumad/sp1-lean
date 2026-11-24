import SP1Clean.FormalModel.Contracts.WriteEffects

/-! # Private byte and stream placement state for WRITE

A byte is identified by the full incoming clock and its absolute guest address. A packet
cursor holds the most recently consumed address, permitting the largest guest byte to be a
terminal state without wrapping the exclusive endpoint. The output position counts bytes
already written within the selected stream or hint.
-/

namespace SP1Clean.WriteEffects

/-- A sink uses 1/2/13 for the fixed output streams, 3 for a fixed hook request, 14 for a fresh
direct hint, or 0 for ignored output. Owner is the reply ordinal or the new hint node pointer. -/
structure Placement (F : Type) where
  /-- Incoming clock identifying the WRITE packet. -/
  clock : fields 3 F
  /-- Output route, including direct hints and ignored descriptors. -/
  sink : F
  /-- Reply ordinal for a hook or node pointer for a direct hint. -/
  owner : fields 3 F
  /-- Guest address immediately preceding the next byte to consume. -/
  address : fields 3 F
  /-- Number of bytes already consumed in the assigned stream. -/
  position : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Placement

/-- Link successive byte positions within one packet. -/
def positionChannel {p : Nat} : Channel (ZMod p) Placement where
  name := "sp1.native.write_byte_position"
  Guarantees _ _ := True

end SP1Clean.WriteEffects
