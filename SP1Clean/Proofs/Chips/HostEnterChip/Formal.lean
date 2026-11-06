import SP1Clean.Native.Chips.HostEnterChip.Defs
import Clean.Utils.Tactics

/-! # The zero-effect native control handler

The handler checks the canonical call and zero result with no witness cells. The same semantic
contract supplies local completeness, and no constructor needs auxiliary comparison columns.
-/

namespace SP1Clean.HostEnterChip

open Circuit

variable {p : ℕ} [Fact p.Prime]

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.enter"
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := Spec input
  channelsWithRequirements := [HostCallChip.channel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel, codeWord]
    simpa only [Vector.map_id', codeWord, circuit_norm] using h_holds
  completeness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel, codeWord]
    simpa only [Vector.map_id', Spec, codeWord, circuit_norm] using h_assumptions
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    simp [main, circuit_norm, HostCallChip.channel]

end SP1Clean.HostEnterChip
