import SP1Clean.Proofs.Chips.FixedProgramProvider.Preprocessed
import SP1Clean.Model.Semantics.Truth
import SP1Clean.Proofs.Sail.InstructionDecode
import ToClean.Air.ChannelClosure

/-! # Authentic Program rows from fixed AIR constraints

The checked image computes the complete fixed table. Its circuit contract and the uniform
Sail decoder theorem establish actual ROM meaning, independently of prover data and lookup
multiplicity. This bridge needs no decoder certificate or semantic provider-validity premise.
-/

namespace SP1Clean.FixedProgramProvider.Preprocessed

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Computed membership names the actual ROM instruction and its official Sail decode. -/
theorem programRow_committed {image : ProgramImage} (valid : image.Valid)
    {message : Channels.ProgramMsg (ZMod p)} (member : message ∈ image.programRows) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg message) := by
  obtain ⟨entry, member, decoded⟩ := (image.mem_programRows message).mp member
  obtain ⟨row, decodedRow, messageEq⟩ := Option.map_eq_some_iff.mp decoded
  have rowEq : Semantics.rowOfMsg message = row := by rw [← messageEq]; rfl
  rw [rowEq]
  have bounds : 2 ^ 16 ≤ entry.1.toNat ∧ entry.1.toNat + 4 ≤ 2 ^ 48 :=
    (valid.2.1 entry member).2.1
  exact ProgramTable.row_committed_of_decode SailDecode.instructionDecode_agrees
    (image.fetchWord_of_mem valid member) (by omega) decodedRow

/-- The fixed-column replacement authenticates every counted fetch. Its empty-table padding
has zero count and never supplies a ROM instruction. -/
theorem spec_committed {image : ProgramImage} (valid : image.Valid)
    {input : Input (ZMod p)} {data : ProverData (ZMod p)}
    (spec : (circuit image).Spec input () data)
    (active : input.2 ≠ 0) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg input.1) := by
  apply programRow_committed valid
  exact (circuit_spec image input () data).mp spec active

/-- The physical fixed prefix authenticates every nonzero provider contribution. The empty
inventory's inert row cannot supply a counted fetch. -/
theorem table_committed {image : ProgramImage} (valid : image.Valid)
    (table : Table (ZMod p))
    (same : table.component = component image)
    (consistent : table.DataConsistency) (constraints : table.Constraints)
    (row : Array (ZMod p)) (member : row ∈ table.table)
    (active : (valueFromOffset Input 0
      (table.environment row)).2 ≠ 0) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg (valueFromOffset Input 0
        (table.environment row)).1) := by
  have spec := (table_spec_and_requirements image
    table same consistent constraints).1 row member
  rw [same] at spec
  exact spec_committed valid spec active

end SP1Clean.FixedProgramProvider.Preprocessed
