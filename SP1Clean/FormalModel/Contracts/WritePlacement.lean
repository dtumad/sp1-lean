import SP1Clean.FormalModel.Contracts.WriteEffects

/-! # Private byte and stream placement state for WRITE

A byte is identified by the full incoming clock and its absolute guest address. A packet
cursor holds the most recently consumed address, permitting the largest guest byte to be a
terminal state without wrapping the exclusive endpoint. The output position counts bytes
already written within the selected stream or hint.
-/

namespace SP1Clean.WriteEffects

structure ByteRead (F : Type) where
  clock : fields 3 F
  key : fields 3 F
  value : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas ByteRead

def byteChannel {p : Nat} : Channel (ZMod p) ByteRead where
  name := "sp1.native.write_effect_byte"
  Guarantees _ _ := True

/-- The byte walker requests the selected lanes; even words with no selected lanes must be consumed. -/
structure LaneRow (F : Type) where
  octets : Octets F
  selected : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas LaneRow

def LaneRow.lane {F : Type} [Add F] (r : LaneRow F) (i : Fin 8) (offset : F) : ByteRead F :=
  ⟨r.octets.clock, Address.offset r.octets.key offset, r.octets.bytes[i]⟩

/-- A sink uses 1/2/13 for the fixed output streams, 3 for a fixed hook request, 14 for a fresh
direct hint, or 0 for ignored output. Owner is the reply ordinal or the new hint node pointer. -/
structure Placement (F : Type) where
  clock : fields 3 F
  sink : F
  owner : fields 3 F
  address : fields 3 F
  position : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Placement

def positionChannel {p : Nat} : Channel (ZMod p) Placement where
  name := "sp1.native.write_byte_position"
  Guarantees _ _ := True

/-- Fresh-node byte ownership during a direct WRITE to FD_HINT. -/
structure NodeByte (F : Type) where
  pointer : fields 3 F
  offset : fields 3 F
  value : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas NodeByte

def nodeByteChannel {p : Nat} : Channel (ZMod p) NodeByte where
  name := "sp1.native.write_node_byte"
  Guarantees _ _ := True

/-- Consume one byte of the cursor's current stream. The guest byte is at the next address;
the stream byte is at the current zero-based position. -/
structure ByteStep (F : Type) where
  previous : Placement F
  nextAddress : fields 3 F
  nextPosition : fields 3 F
  value : F
  ignored : F
  direct : F
deriving ProvableStruct
provable_struct_eval_lemmas ByteStep

def ByteStep.next {F : Type} (b : ByteStep F) : Placement F :=
  {b.previous with address := b.nextAddress, position := b.nextPosition}

def ByteStep.read {F : Type} (b : ByteStep F) : ByteRead F :=
  ⟨b.previous.clock, b.nextAddress, b.value⟩

def ByteStep.nodeByte {F : Type} (b : ByteStep F) : NodeByte F :=
  ⟨b.previous.owner, b.previous.position, b.value⟩

end SP1Clean.WriteEffects
