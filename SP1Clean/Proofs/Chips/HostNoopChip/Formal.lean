import SP1Clean.Native.Chips.HostNoopChip.Defs
import Clean.Utils.Tactics

/-! # The zero-effect native control handler

The handler checks the canonical call and return with no witness cells. The same semantic
contract supplies local completeness, and no constructor needs auxiliary comparison columns.
-/

namespace SP1Clean.HostNoopChip

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- The complete no-effect host circuit for the chosen released call. -/
def circuit (kind : Kind) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := match kind with | .enter => "sp1.native.enter" | .verify => "sp1.native.verify"
  main := main kind
  elaborated := elaborated kind
  Spec input _ _ := Spec kind input
  ProverAssumptions input _ _ := Spec kind input
  channelsWithRequirements := [HostCallChip.channel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel]
    simpa only [Vector.map_id', circuit_norm] using h_holds
  completeness := by
    circuit_proof_start [Gadgets.Equality.circuit, HostCallChip.channel]
    simpa only [Vector.map_id', Spec, circuit_norm] using h_assumptions

end SP1Clean.HostNoopChip
