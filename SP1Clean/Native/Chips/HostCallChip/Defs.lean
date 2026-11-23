import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal

/-! # An ECALL instruction with its host handoff

The full-register profile guard and released instruction supply the entire row.
One gated host receipt is appended to the original instruction interactions.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def main (input : Var SyscallInstrsChip.Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← CoreSyscallChip.circuit input
  channel.pushIf input.is_real (message input)

/-- The physical operations preserve the guarded instruction as a bundled subcircuit. -/
theorem operations_eq (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    (main input).operations offset =
      [.subcircuit (CoreSyscallChip.circuit.toSubcircuit offset input),
       .interact (channel.pushedIf input.is_real (message input)).toRaw] := by
  rfl

@[circuit_norm] theorem core_requirements :
    (CoreSyscallChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] := rfl

@[circuit_norm] theorem core_guarantees :
    (CoreSyscallChip.circuit (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
        exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] := rfl

attribute [local circuit_norm] channel

instance elaborated : ElaboratedCircuit (ZMod p) SyscallInstrsChip.Inputs unit main := by
  elaborate_circuit

/-- Only the existing guarded instruction supplies lookup guarantees. -/
@[circuit_norm] theorem channelsWithGuarantees_eq :
    (elaborated (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
        exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] := rfl

end SP1Clean.HostCallChip
