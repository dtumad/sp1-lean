import SP1Clean.FormalModel.Contracts.WriteEffects

/-! # Private byte and stream placement state for WRITE

A byte is identified by the full incoming clock and its absolute guest address. A packet
cursor holds the most recently consumed address, permitting the largest guest byte to be a
terminal state without wrapping the exclusive endpoint. The output position counts bytes
already written within the selected stream or hint.
-/

namespace SP1Clean.WriteEffects

/-- A selected guest byte identified by its absolute address and incoming WRITE clock. -/
structure ByteRead (F : Type) where
  /-- Clock of the WRITE that requested the byte. -/
  clock : fields 3 F
  /-- Absolute address of this byte within the guest. -/
  key : fields 3 F
  /-- Value decoded from its observed 64-bit word. -/
  value : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas ByteRead

/-- Join selected guest-word lanes to the destination cursor. -/
def byteChannel {p : Nat} : Channel (ZMod p) ByteRead where
  name := "sp1.native.write_effect_byte"
  Guarantees _ _ := True

/-- The byte walker requests the selected lanes; even words with no selected lanes must be consumed. -/
structure LaneRow (F : Type) where
  /-- The complete word recovered from a physical memory receipt. -/
  octets : Octets F
  /-- Per-byte flags selecting the intersection with the requested interval. -/
  selected : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas LaneRow

/-- Identify the selected byte by its absolute guest address and call clock. -/
def LaneRow.lane {F : Type} [Add F] (r : LaneRow F) (i : Fin 8) (offset : F) : ByteRead F :=
  ⟨r.octets.clock, Address.offset r.octets.key offset, r.octets.bytes[i]⟩

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

/-- Fresh-node byte ownership during a direct WRITE to FD_HINT. -/
structure NodeByte (F : Type) where
  /-- Identity of the freshly allocated immutable hint node. -/
  pointer : fields 3 F
  /-- Zero-based byte position within that node. -/
  offset : fields 3 F
  /-- Byte read from the guest for this position. -/
  value : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas NodeByte

/-- Authorize bytes of a direct hint at their fresh node and offset. -/
def nodeByteChannel {p : Nat} : Channel (ZMod p) NodeByte where
  name := "sp1.native.write_node_byte"
  Guarantees _ _ := True

/-- Consume one byte of the cursor's current stream. The guest byte is at the next address;
the stream byte is at the current zero-based position. -/
structure ByteStep (F : Type) where
  /-- Cursor before consuming this guest byte. -/
  previous : Placement F
  /-- Address of the byte consumed by this step. -/
  nextAddress : fields 3 F
  /-- Stream position immediately after consuming the byte. -/
  nextPosition : fields 3 F
  /-- Value shared by the guest read and its destination. -/
  value : F
  /-- One when this route discards the byte. -/
  ignored : F
  /-- One when the byte populates a new direct hint. -/
  direct : F
deriving ProvableStruct
provable_struct_eval_lemmas ByteStep

/-- Advance the guest and stream positions while retaining packet identity. -/
def ByteStep.next {F : Type} (b : ByteStep F) : Placement F :=
  {b.previous with address := b.nextAddress, position := b.nextPosition}

/-- The original guest byte required at this cursor. -/
def ByteStep.read {F : Type} (b : ByteStep F) : ByteRead F :=
  ⟨b.previous.clock, b.nextAddress, b.value⟩

/-- Attach this guest byte to the newly allocated node. -/
def ByteStep.nodeByte {F : Type} (b : ByteStep F) : NodeByte F :=
  ⟨b.previous.owner, b.previous.position, b.value⟩

end SP1Clean.WriteEffects
