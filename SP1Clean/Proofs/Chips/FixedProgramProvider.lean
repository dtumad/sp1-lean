import SP1Clean.Proofs.Chips.ProgramProviderChip

/-! # A program provider bound to concrete fixed rows

The original provider establishes row-local range facts but does not constrain the program's
opcode and operand contents. This wrapper composes that provider and a static-table lookup on
the complete message. The fixed table is an ensemble parameter, independent of prover data.

Its specification records actual fixed-ROM membership. A native program decoder must supply the
table and prove its rows describe the checked program; that construction is separate from this
whole-row circuit proof. Zero-multiplicity padding also uses a valid fixed row.
-/

namespace SP1Clean.FixedProgramProvider

open Circuit
open SP1Clean.Channels (ProgramMsg programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The existing range-checked provider, strengthened with complete fixed-program membership. -/
def circuit (rom : StaticTable (ZMod p) ProgramMsg) :
    GeneralFormalCircuit (ZMod p) ProgramProviderChip.Inputs unit where
  main input := do
    let _ ← ProgramProviderChip.circuit input
    lookup rom.toTable input.toMessage
  Spec input _ _ := ProgramMsg.RowSpec input.toMessage ∧ rom.Spec input.toMessage
  ProverAssumptions input _ _ := ProgramMsg.RowSpec input.toMessage ∧ rom.Spec input.toMessage
  channelsWithRequirements := [programChannel.toRaw]
  soundness := by
    circuit_proof_start [ProgramProviderChip.circuit, ProgramProviderChip.Inputs.toMessage]
    exact h_holds
  completeness := by
    circuit_proof_start [ProgramProviderChip.circuit, ProgramProviderChip.Inputs.toMessage]
    exact h_assumptions

end SP1Clean.FixedProgramProvider
