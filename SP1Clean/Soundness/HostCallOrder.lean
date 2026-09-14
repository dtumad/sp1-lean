import SP1Clean.Soundness.HostCallLedger
import SP1Clean.Soundness.LocalCoreEventUniqueness

/-! # Instruction clock uniqueness at the host handoff

Projection of the wrapper's physical active rows onto the local assembly's actual syscall
inventory transfers the proved CPU clock uniqueness. The projection is an explicit installation
seam: the current local ensemble still registers the original syscall component.
The local-witness corollary assumes that ensemble's complete balance. Installation of active
host RAM effects must reuse State/Byte chronology directly: dropping effect tables does not
in general preserve the original ensemble's Memory balance.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Channels Model.Core NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Exact active-row projection identifies every wrapper call with a distinct actual CPU event.
It neither assumes handler uniqueness nor changes the local shard's arbitrary endpoints. -/
theorem hostCalls_clocks_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p))
    (projected : ((HostCallLedger.activeRows table).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real)) :
    ((HostCallLedger.calls table).map HostCallLedger.clock).Nodup := by
  have unique := executionRows_clocks_nodup witness constraints balanced
  simp only [executionRows, List.map_append, List.map_map, Function.comp_def] at unique
  have syscalls := (List.nodup_append.mp unique).2.1
  rw [← projected] at syscalls
  simpa only [HostCallLedger.calls, List.map_map, Function.comp_def, ExecutionRow.edge,
    SyscallInstrsChip.statePulledMessage, HostCallLedger.clock, HostCallLedger.call,
    HostCallChip.Inputs.message] using syscalls

end SP1Clean.Soundness.LocalCore
