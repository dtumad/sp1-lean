import SP1Clean.Proofs.Chips.HostCallChip.Formal
import ToClean.Circuit.InteractionRecovery

/-! # The instruction-to-host ledger

The physical ECALL preserves every guarded instruction interaction and adds one host receipt.
Each receipt uses the incoming instruction clock, including repeated calls and disabled rows.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Raw constraints retain the original instruction and its full-register code check. -/
theorem instruction_of_constraints (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (constraints : ((main input).operations offset).ConstraintsHold env) :
    ((CoreSyscallChip.circuit.main input).operations offset).ConstraintsHold env := by
  rw [← Circuit.constraintsHold_toFlat_iff, operations_eq] at constraints
  simp only [circuit_norm] at constraints
  have original := (FlatOperation.constraintsHold_append.mp constraints).1
  rw [← Circuit.constraintsHold_toFlat_iff]
  simpa only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat] using original

/-- The physical row writes exactly one gated receipt on the shared host channel. -/
theorem main_host_interactions (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith channel.toRaw =
      [(channel.pushedIf input.is_real (message input)).toRaw] := by
  have coreEmpty := InteractionRecovery.interactionsWith_main_eq_nil
    CoreSyscallChip.circuit.base channel.toRaw input offset
    (by simp [core_guarantees, core_requirements, circuit_norm, channel,
      byteChannel, memoryChannel, stateChannel, programChannel, exitChannel, syscallChannel,
      publicValuesChannel])
  rw [operations_eq]
  simp only [Operations.interactionsWith, Circuit.operations] at coreEmpty ⊢
  simp [circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append, coreEmpty]

/-- All other channel occurrences agree literally with the guarded instruction.
This includes every Memory pull and push and all zero-multiplicity rows. -/
theorem main_other_interactions (target : RawChannel (ZMod p)) (notHost : target ≠ channel.toRaw)
    (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target =
      ((CoreSyscallChip.circuit.main input).operations offset).interactionsWith target := by
  rw [operations_eq]
  simp [Operations.interactionsWith, Circuit.operations, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, List.filter_append, Ne.symm notHost]

end SP1Clean.HostCallChip
