import SP1Clean.Proofs.Operations.WriteCellEndpoint
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Native.Operations.AddressOrder

/-! # Native WRITE buffer span and aligned-word cursor

Each header produces one start and consumes one exclusive stop. A word row consumes a
cursor, reads one aligned guest word at the same clock, and produces its exact successor.
-/

namespace SP1Clean.WriteBuffer

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The original address with its floor-division witness. -/
def Span.startEndpoint {F : Type} (s : Span F) : Endpoint F := ⟨s.header.address, s.startQuotients, s.first⟩
/-- The exclusive full byte endpoint with its ceiling-division witness. -/
def Span.endEndpoint {F : Type} (s : Span F) : Endpoint F := ⟨s.finish, s.endQuotients, s.stop⟩

/-- First possible guest RAM cell expressed as a word index. -/
def minimum : fields 3 (ZMod p) := Address.ofNat (2 ^ 13)

/-- Fixed length bit, checked independently of the four-limb adder, excludes 64-bit wrap. -/
def spanMain (s : Var Span (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← Endpoint.circuit false s.startEndpoint
  let _ ← Endpoint.circuit true s.endEndpoint
  assertion WordRangeCheck.circuit s.header.length
  assertBool s.header.length[3]
  assertion AddOperation.circuit ⟨s.header.address, s.header.length, ⟨s.finish⟩, 1⟩
  assertion AddressOrder.circuit ⟨const minimum, s.first⟩
  WritePacket.channel.pull s.header
  channel.push s.source
  channel.pull s.target
  effectHeaderChannel.push s.header

instance spanElaborated : ElaboratedCircuit (ZMod p) Span unit spanMain := by elaborate_circuit

/-- All words are observed through the native read-only probe. -/
def Step.division {F : Type} [Zero F] (s : Step F) : AddressDiv8.Inputs F :=
  ⟨Address.asWord s.read.key, s.quotients⟩

/-- The cursor index and the RAM key are bound by division of the actual read receipt. -/
def stepMain (s : Var Step (ZMod p)) : Circuit (ZMod p) Unit := do
  let div ← AddressDiv8.circuit s.division
  div.quotient === s.index
  assertZero div.remainder
  assertion AddrAddOperation.circuit ⟨Address.asWord s.index, #v[1, 0, 0, 0], ⟨s.next⟩, 1⟩
  channel.pull s.source
  WriteProbe.readChannel.pull s.read
  channel.push s.target
  wordChannel.push s.read

instance stepElaborated : ElaboratedCircuit (ZMod p) Step unit stepMain := by elaborate_circuit

end SP1Clean.WriteBuffer
