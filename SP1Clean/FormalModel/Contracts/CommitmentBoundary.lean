import SP1Clean.FormalModel.Contracts.CommitmentStatement
import SP1Clean.FormalModel.Contracts.PublicValues

/-! # Canonical public encoding of the immutable commitment statement

Public-output words use four little-endian bytes. Deferred words are canonical field elements;
`WellFormed` rules out reduction modulo the characteristic. The named-field adapter leaves the
rest of SP1's shard record, including previous commitments and cross-shard fields, explicit.
-/

namespace SP1Clean.CommitmentBoundary

open Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- Public digest words flattened to canonical little-endian bytes. -/
def committed (statement : CommitmentStatement) : Vector (ZMod p) 32 :=
  Vector.ofFn fun index =>
    ((statement.committed[index.val / 4]'(by omega)).toNat / 2 ^ (8 * (index.val % 4)) % 256 : ℕ)

/-- Deferred digest words embedded in the field; `WellFormed` prevents reduction. -/
def deferred (statement : CommitmentStatement) : Vector (ZMod p) 8 :=
  statement.deferred.map fun word => (word.toNat : ℕ)

/-- Public encoding agrees with the verifier-owned, well-formed statement. -/
def Spec (statement : CommitmentStatement) (input : SP1PublicIO (ZMod p)) : Prop :=
  statement.WellFormed p ∧ input.committed_value_digest = committed statement ∧
    input.deferredProofsDigest = deferred statement ∧
    input.commitSyscall = (if statement.commit then 1 else 0) ∧
    input.commitDeferredSyscall = (if statement.commitDeferred then 1 else 0)


/-- Bind only the current commitment fields of SP1's full named public-values record. -/
def publicValues (statement : CommitmentStatement) (values : SP1PublicValues (ZMod p)) :
    SP1PublicValues (ZMod p) :=
  { values with
    committed_value_digest := Vector.ofFn fun word => Vector.ofFn fun byte =>
      (committed statement)[4 * word.val + byte.val]'(by omega)
    deferred_proofs_digest := deferred statement
    commit_syscall := if statement.commit then 1 else 0
    commit_deferred_syscall := if statement.commitDeferred then 1 else 0 }

end SP1Clean.CommitmentBoundary
