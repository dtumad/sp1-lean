import SP1Clean.Proofs.Chips.DecodedProgramProvider
import SP1Clean.Proofs.Chips.FixedProgramProvider.Preprocessed
import SP1Clean.Model.Semantics.Truth
import SP1Clean.Proofs.Sail.InstructionDecode
import ToClean.Air.ChannelClosure

/-! # Authentic Program rows from fixed AIR constraints

The checked image computes the complete fixed table. Its circuit contract and the uniform
Sail decoder theorem establish actual ROM meaning, independently of prover data and lookup
multiplicity. This bridge needs no decoder certificate or semantic provider-validity premise.
-/

namespace SP1Clean.DecodedProgramProvider

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

/-- The lookup provider authenticates every message, independently of prover data and count. -/
theorem spec_committed {image : ProgramImage} (valid : image.Valid)
    {input : ProgramProviderChip.Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (spec : (circuit image).Spec input () data) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg input.toMessage) := by
  apply programRow_committed valid
  exact (image.mem_programRows _).mpr ((image.programTable_spec _).mp spec.2)

/-- The fixed-column replacement authenticates every counted fetch. Its empty-table padding
has zero count and never supplies a ROM instruction. -/
theorem preprocessed_spec_committed {image : ProgramImage} (valid : image.Valid)
    {input : FixedProgramProvider.Preprocessed.Input (ZMod p)} {data : ProverData (ZMod p)}
    (spec : (FixedProgramProvider.Preprocessed.circuit image).Spec input () data)
    (active : input.2 ≠ 0) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg input.1) := by
  apply programRow_committed valid
  unfold FixedProgramProvider.Preprocessed.circuit at spec
  split at spec <;> exact spec active

/-- A physical provider row satisfying its raw constraints names an authentic instruction in
this image. Fixed lookups are part of `ConstraintsHold`; channel balance is not a premise. -/
theorem constraints_committed {image : ProgramImage} (valid : image.Valid)
    (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit image, Assumptions := (circuit image).Assumptions } : Component (ZMod p)).operations.ConstraintsHold env) :
    Soundness.Target.committedInROM (image.toGuestProgram valid)
      (Semantics.rowOfMsg (({ circuit := circuit image, Assumptions := (circuit image).Assumptions } : Component (ZMod p)).rowInput env).toMessage) := by
  exact spec_committed valid (({ circuit := circuit image, Assumptions := (circuit image).Assumptions } : Component (ZMod p)).weakSoundness_of_no_guarantees
    rfl (by trivial) constraints).1

/-- The evaluated provider ledger has exactly the complete committed message as its payload. -/
theorem program_interaction_payload (image : ProgramImage) (env : Environment (ZMod p))
    (interaction : Interaction (ZMod p))
    (member : interaction ∈ ({ circuit := circuit image, Assumptions := (circuit image).Assumptions } : Component (ZMod p)).operations.interactionValuesWith
      Channels.programChannel.toRaw env) :
    interaction.msg = (toElements
      (({ circuit := circuit image, Assumptions := (circuit image).Assumptions } : Component (ZMod p)).rowInput env).toMessage).toArray :=
  FixedProgramProvider.program_interaction_payload image.programTable env interaction member

end SP1Clean.DecodedProgramProvider
