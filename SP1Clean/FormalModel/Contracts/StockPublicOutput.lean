import Clean.Specs.SHA256
import ToClean.Specs.BLAKE3
import SP1Clean.FormalModel.Contracts.CommitmentBoundary
import SP1Clean.Semantics.Host.HostIO

/-! # Public output checked by the released Core and Compressed SDK

The SDK takes the canonical exit code and low eight bits of each committed digest limb from
the proof's public record. It hashes the supplied bytes with SHA-256 and BLAKE3 and accepts
either digest. Core selects the last shard. Compressed reads the same fields directly from
its recursion record. These predicates apply after version and public-record layout checks.
Cryptographic verification and native host execution have their own contracts.
-/

namespace SP1Clean.FormalModel.StockPublicOutput

open Semantics

/-- Fields shared by the Core and Compressed public-output checks in the SP1 SDK. -/
structure Claim where
  /-- Canonical field representative of the exit code. -/
  exitCode : Nat
  /-- Digest bytes in SDK iteration order. -/
  digest : Vector (BitVec 8) 32
deriving DecidableEq, Repr

/-- Extract the two fields from either typed record. Rust casts each field limb to `u8`. -/
def ofFields {p : Nat} (exitCode : ZMod p) (words : Vector (SP1Word32 (ZMod p)) 8) : Claim :=
  ⟨exitCode.val, words.flatten.map (fun limb => BitVec.ofNat 8 limb.val)⟩

/-- The final Core shard supplies the SDK's public output claim. -/
def ofCore {p : Nat} (values : SP1PublicValues (ZMod p)) : Claim :=
  ofFields values.exit_code values.committed_value_digest

/-- Decode the same byte representation on the flat native public boundary. -/
def ofNative {p : Nat} (header : SP1StateBoundary (ZMod p)) : Claim :=
  ⟨header.exit_code.val, header.committed_value_digest.map (fun limb => BitVec.ofNat 8 limb.val)⟩

/-- The commitment adapter fills precisely the digest seen by the SDK. -/
theorem commitment_projection {p : Nat} [Fact p.Prime] (statement : CommitmentStatement)
    (values : SP1PublicValues (ZMod p)) (header : SP1StateBoundary (ZMod p))
    (bound : CommitmentBoundary.Spec statement header) (exitCode : values.exit_code = header.exit_code) :
    ofCore (CommitmentBoundary.publicValues statement values) = ofNative header := by
  apply congrArg₂ Claim.mk (congrArg ZMod.val exitCode)
  change ((CommitmentBoundary.committed statement).toChunks (n := 8) 4).flatten.map _ = _
  rw [Vector.toChunks_flatten, bound.2.1]

/-- Expected status values exposed by the released executor's `StatusCode` API. -/
inductive ExpectedStatus where
  | success | panic | invalidHint | any
deriving DecidableEq, Repr

/-- The experimental build permits panic and invalid-hint results when requested. -/
def ExpectedStatus.accepts (expected : ExpectedStatus) (experimental : Bool) (code : Nat) : Bool :=
  (experimental || code == 0) && match expected with
    | .success => code == 0
    | .panic => code == 1
    | .invalidHint => code == 3
    | .any => code == 0 || code == 1 || code == 3

/-- SHA-256 serializes each digest word most-significant byte first. -/
def sha256 (bytes : Bytes) : Vector (BitVec 8) 32 :=
  (Specs.SHA256.sha256 (bytes.map BitVec.toNat)).flatMap fun word =>
    Vector.ofFn fun i : Fin 4 => BitVec.ofNat 8 (word >>> (8 * (3 - i.val)))

/-- BLAKE3 serializes each digest word least-significant byte first. -/
def blake3 (bytes : Bytes) : Vector (BitVec 8) 32 :=
  (Specs.BLAKE3.blake3 bytes).flatMap fun word =>
    Vector.ofFn fun i : Fin 4 => BitVec.ofNat 8 (word >>> (8 * i.val))

/-- Public-output checks on a typed proof record and the bundle's raw public bytes.
The SDK defaults to successful exit. -/
def Claim.accepts (claim : Claim) (bytes : Bytes) (expected : ExpectedStatus := .success)
    (experimental : Bool := false) : Bool :=
  expected.accepts experimental claim.exitCode &&
    (claim.digest == sha256 bytes || claim.digest == blake3 bytes)

/-- Public-output check for a typed list of Core shards. An empty proof has no final record. -/
def acceptsCore {p : Nat} (shards : List (SP1PublicValues (ZMod p))) (bytes : Bytes)
    (expected : ExpectedStatus := .success) (experimental : Bool := false) : Bool :=
  shards.getLast?.any fun final => (ofCore final).accepts bytes expected experimental

/-- Earlier Core shards do not participate in the SDK's terminal output check. -/
theorem acceptsCore_append {p : Nat} (earlier : List (SP1PublicValues (ZMod p)))
    (final : SP1PublicValues (ZMod p)) (bytes : Bytes) (expected : ExpectedStatus) (experimental : Bool) :
    acceptsCore (earlier ++ [final]) bytes expected experimental =
      (ofCore final).accepts bytes expected experimental := by
  simp [acceptsCore]

end SP1Clean.FormalModel.StockPublicOutput
