import SP1Clean.Semantics.Host.WriteStreamRecords
import SP1Clean.FormalModel.Contracts.WriteChronology

/-! # Natural byte and reply positions of a chronological WRITE transcript -/

namespace SP1Clean.WriteEffects
open Semantics

/-- The public byte string receiving this packet, when the route has an endpoint-owned payload. -/
def destinationKey (route : WriteRoute) (reply : Nat) : Option StreamKey :=
  match route with
  | .stdout => some .stdout
  | .stderr => some .stderr
  | .publicValues => some .publicOutput
  | .hook _ => some (.request reply)
  | .hint | .ignored => none

/-- The four stream lengths carried between successive dispatches. -/
structure StreamCounts where
  /-- Bytes written to stdout during this shard. -/
  stdout : Nat
  /-- Bytes written to stderr during this shard. -/
  stderr : Nat
  /-- Bytes appended to the public-values stream. -/
  publicValues : Nat
  /-- Replies consumed by WRITE hooks. -/
  hooks : Nat
deriving Inhabited, DecidableEq

/-- Project a complete stream transcript to the four physical cursor positions. -/
def StreamCounts.ofStreams (s : WriteStreams) : StreamCounts :=
  ⟨s.stdout.length,s.stderr.length,s.publicOutput.length,s.hooks.length⟩

/-- Decode the four natural counters from the actual physical stream cursor. -/
def StreamCounts.ofCursor {p : Nat} (c : StreamCursor (ZMod p)) : StreamCounts :=
  ⟨Address.toNat c.stdout,Address.toNat c.stderr,Address.toNat c.publicOutput,Address.toNat c.replies⟩

/-- The next guest byte appends to its output stream or starts at zero for a fresh request. -/
def StreamCounts.offset (s : StreamCounts) : WriteRoute → Nat
  | .stdout => s.stdout
  | .stderr => s.stderr
  | .publicValues => s.publicValues
  | _ => 0

/-- Advance exactly the selected external stream or consume one supplied hook reply. -/
def StreamCounts.record (s : StreamCounts) (route : WriteRoute) (length : Nat) : StreamCounts :=
  match route with
  | .stdout => {s with stdout := s.stdout + length}
  | .stderr => {s with stderr := s.stderr + length}
  | .publicValues => {s with publicValues := s.publicValues + length}
  | .hook _ => {s with hooks := s.hooks + 1}
  | _ => s

end SP1Clean.WriteEffects
