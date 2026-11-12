import SP1Clean.Soundness.LocalCoreMemoryOrder
import SP1Clean.Soundness.CoreRowTransport

/-! # The local mixed carrier after refresh elimination

The carrier passed to grounding keeps every ordinary/HALT/syscall occurrence, rewrites only prior
Memory records, and uses canonical State endpoints. Its complete structural row contract and
semantic step/frame transport are derived from the checked image and raw constraints/balance.
The original rows' actual execution facts remain the next semantic obligation.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow canonicalRow rewrittenRows rewritten_core
  rewriteRows_forall₂ rewritten_memory syscall_readsInWindow_of_committed)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem syscallRows_readsInWindow {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ReadsInWindow (syscallRowFacts row) := by
  obtain ⟨mapped, real⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have committed := syscall_program_committed_of_balance valid witness constraints balanced physicalMem (of_decide_eq_true real)
  exact syscall_readsInWindow_of_committed _ _ committed

/-- All original execution reads lie within their location's pre-effect window, with syscall
read times retained. Operand addresses for system rows come from the checked Program ledger. -/
theorem executionRows_readsInWindow_of_program {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {event : ExecutionRow p} (member : event ∈ executionRows witness) :
    ReadsInWindow (event.facts witness.data) := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, _, rfl⟩ | ⟨halt, _, rfl⟩) | ⟨syscall, member, rfl⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · intro pull pullMem
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp pullMem
    exact ⟨le_rfl, Nat.le_add_right _ _⟩
  · exact syscallRows_readsInWindow valid witness constraints balanced member

end SP1Clean.Soundness.LocalCore
