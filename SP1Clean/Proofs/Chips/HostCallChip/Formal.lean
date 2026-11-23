import SP1Clean.Native.Witgen.StateDemand
import SP1Clean.Native.Chips.HostCallChip.Defs

/-! # Soundness and completeness of the instruction-to-host handoff

The wrapper preserves the semantic and completeness contracts of the guarded instruction.
Its outgoing receipt is computed entirely from the same row's inputs.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def circuit : GeneralFormalCircuit (ZMod p) SyscallInstrsChip.Inputs unit where
  name := "sp1.native.host_call"
  computableWitnesses := by computable_witnesses
  main
  elaborated
  Spec input _ _ := CoreSyscallChip.Spec input
  ProverAssumptions := CoreSyscallChip.circuit.ProverAssumptions
  soundness := by
    circuit_proof_start [CoreSyscallChip.circuit, channel]
    exact h_holds
  completeness := by
    circuit_proof_start [CoreSyscallChip.circuit, channel]
    exact h_assumptions
  channelsWithRequirements := [memoryChannel.toRaw, channel.toRaw]

/-- Host calls use the instruction's existing unit-demand State routing. -/
def generation : Air.Flat.WitnessGeneration.Generation (ZMod p) SyscallInstrsChip.Inputs :=
  Native.Witgen.stateDemand (circuit (p := p)).name (·.state) (·.is_real)

end SP1Clean.HostCallChip
