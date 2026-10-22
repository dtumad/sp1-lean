import SP1Clean.FormalModel.Contracts.CommitmentStatement
import ToClean.Air.StaticProvider

/-! # Verifier-fixed commitment declarations

Only the sixteen declaration counts are prover-owned. Clean's fixed-table provider retains all
rows, including unused slots, and prevents changing a word or flag to match a conflicting call.
-/

namespace SP1Clean.CommitmentDeclaration

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- The complete padded declaration inventory fits the upstream table index. -/
theorem height_bounded (statement : CommitmentStatement) :
    (table (p := p) statement).height < UInt64.size := by
  have length : (table (p := p) statement).length = 16 := by
    simp [table, StaticTable.ofRows, rows]
  have padded := (table (p := p) statement).height_lt_double
  rw [length] at padded
  norm_num [UInt64.size] at *
  omega

/-- The public statement supplies the fixed prefix; counts can only reuse those declarations. -/
def source (statement : CommitmentStatement) : Component (ZMod p) :=
  (table statement).payloadComponent channel (fun _ _ _ => trivial) (height_bounded statement)

/-- Physical preprocessing authenticates every nonzero source occurrence. -/
theorem source_authenticates (statement : CommitmentStatement) (physical : Table (ZMod p))
    (same : physical.component = source statement) (consistent : physical.DataConsistency)
    (constraints : physical.Constraints) :
    physical.Authenticates channel (fun row => row ∈ rows statement) :=
  (table statement).payload_authenticates channel (fun _ _ _ => trivial)
    (height_bounded statement) physical same consistent constraints

end SP1Clean.CommitmentDeclaration
