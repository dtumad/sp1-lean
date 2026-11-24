import SP1Clean.Native.Chips.WritePacket.Defs

/-! # Soundness and completeness of WRITE packet binding -/

namespace SP1Clean.WritePacket

open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- An active packet binds one instruction and one observed length at the same absolute clock. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_packet_header"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := input.timestamp.Bounded
  channelsWithRequirements := [channel.toRaw]
  soundness := by
    circuit_proof_start [ClockParts.circuit, HostCallChip.channel, WriteProbe.readChannel, channel]
    exact spec_of_bounded ⟨⟨_, _, _, _⟩, input_descriptor, input_address, input_length⟩ h_holds
  completeness := by
    circuit_proof_start [ClockParts.circuit, HostCallChip.channel, WriteProbe.readChannel, channel]
    exact h_assumptions

end SP1Clean.WritePacket
