import SP1Clean.FormalModel.Contracts.WritePacketHeader
import SP1Clean.FormalModel.Contracts.AddressDiv8

/-! # Aligned word coverage of a clock-bound WRITE packet

The endpoints and cursor carry word indices. The exclusive upper index at the end of
48-bit guest memory is representable even though its byte address is one-past memory.
-/

namespace SP1Clean.WriteBuffer

/-- Shared state of one read-only walk at an incoming ECALL clock. -/
structure Cursor (F : Type) where
  /-- Incoming clock, shared by the header and each observed word. -/
  clock : fields 3 F
  /-- Absolute index of the current aligned eight-byte RAM cell. -/
  index : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Cursor

/-- The header seeds and closes one walk per packet; a word row advances it by one. -/
def channel {p : ℕ} : Channel (ZMod p) Cursor where
  name := "sp1.native.write_buffer_cursor"
  Guarantees _ _ := True

/-- Every checked span supplies its complete packet to the host effect receiver, including empty spans. -/
def effectHeaderChannel {p : ℕ} : Channel (ZMod p) WritePacket.Header where
  name := "sp1.native.write_effect_header"
  Guarantees _ _ := True

/-- Every checked word supplies its full clock, aligned RAM key, and value to the effect receiver. -/
def wordChannel {p : ℕ} : Channel (ZMod p) WriteProbe.Read where
  name := "sp1.native.write_buffer_value"
  Guarantees _ _ := True

/-- Natural cell index obtained by rounding the full byte endpoint down or up. -/
def cellIndex (roundUp : Bool) (byte : ℕ) : ℕ := (byte + if roundUp then 7 else 0) / 8

/-- An inclusive byte endpoint in the range from zero to one-past guest memory. -/
structure Endpoint (F : Type) where
  /-- Full four-limb byte endpoint. -/
  byte : Word F
  /-- Partial quotients of its low three limbs. -/
  quotients : fields 3 F
  /-- Claimed floor or ceiling cell index. -/
  index : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Endpoint

/-- The span binds one header to both endpoints of its word interval. -/
structure Span (F : Type) where
  /-- Original ECALL receipt including descriptor and complete length. -/
  header : WritePacket.Header F
  /-- Byte address after adding the original length to the original start. -/
  finish : Word F
  /-- Partial quotients of the original header address. -/
  startQuotients : fields 3 F
  /-- Partial quotients of the exclusive byte endpoint. -/
  endQuotients : fields 3 F
  /-- First word's absolute index, or the empty aligned endpoint. -/
  first : fields 3 F
  /-- Exclusive stop as a word index, including the highest permitted endpoint. -/
  stop : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Span

/-- One physical aligned-word request and its exact cursor edge. -/
structure Step (F : Type) where
  /-- Private receipt for the actual full word. -/
  read : WriteProbe.Read F
  /-- Partial quotients of the aligned RAM address. -/
  quotients : fields 3 F
  /-- Current absolute word index. -/
  index : fields 3 F
  /-- Next absolute word index. -/
  next : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Step

/-- The cursor endpoints emitted by the packet owner. -/
def Span.source {F : Type} (s : Span F) : Cursor F := ⟨s.header.clock, s.first⟩
/-- The stop cursor consumed by the packet owner. -/
def Span.target {F : Type} (s : Span F) : Cursor F := ⟨s.header.clock, s.stop⟩
/-- The word row consumes this cursor. -/
def Step.source {F : Type} (s : Step F) : Cursor F := ⟨s.read.clock, s.index⟩
/-- The word row advances the same packet clock to its exact successor. -/
def Step.target {F : Type} (s : Step F) : Cursor F := ⟨s.read.clock, s.next⟩

end SP1Clean.WriteBuffer
