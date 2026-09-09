import SP1Clean.Model.Core.Boot
import SP1Clean.Model.Semantics.MicroTime

/-! # Native initial-memory records

The initial provider's public contract fixes the value at the actual decoded Memory-bus location
to the native boot state. Address canonicality and zero time are conclusions of the provider,
not assumptions supplied by a trace consumer. Uniqueness is a separate global balance argument.
-/

namespace SP1Clean.MemoryBoundary

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime]

/-- The field encoding of a Memory record's address as a full word. -/
def address {R : Type} [Zero R] (message : MemoryMsg R) : Word R :=
  #v[message.addr0, message.addr1, message.addr2, 0]

/-- The encoded key is range checked and equals the decoded location's canonical address. -/
def CanonicalKey (message : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 (address message) ∧
    Word.toNat (address message) = (MemoryMsg.locOf message).busAddress

/-- An authentic initial record at a canonical register or aligned RAM location. -/
def InitialSpec (image : ProgramImage) (message : MemoryMsg (ZMod p)) : Prop :=
  MemoryMsg.isU64 message ∧ MemoryMsg.ClkBound message ∧
    MemoryMsg.timeNat message = 0 ∧ (MemoryMsg.locOf message).CanonicalAddress ∧
      locContent image.initialSailState (MemoryMsg.locOf message) =
        some (Word.toBitVec64 message.value) ∧ CanonicalKey message

/-- Authentication also preserves the caller's semantic query address. This clause lets a
composed row constructor choose its ordered key before executing the provider's witnesses. -/
def InitialAtSpec (image : ProgramImage) (query : ℕ) (message : MemoryMsg (ZMod p)) : Prop :=
  InitialSpec image message ∧ Word.toNat (address message) = query

end SP1Clean.MemoryBoundary
