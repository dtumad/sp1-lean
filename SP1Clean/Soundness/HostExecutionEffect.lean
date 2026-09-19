import SP1Clean.Model.Core.Execution
import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Proofs.Sail.Advance

/-! # Architectural preservation by concrete host execution

The native host interpreter writes PC/x5 and its explicit byte effect. All other integer registers
and the Sail configuration survive, and the checked memory policy protects every program byte.
These facts apply to every semantic host call, including calls which modify RAM.
-/

namespace SP1Clean.Soundness

open Model.Core Target LeanRV64D.Defs

private theorem host_apply_configured (execution : HostExecution) (state : SailState) (pc : BitVec 64)
    (configured : SailConfigured state) : SailConfigured (execution.apply state pc) := by
  refine SP1Clean.Advance.SailConfigured.congr configured ?_ ?_
  · exact SailState.isInitialized_insert _ (SailState.isInitialized_insert state configured.init _ _) _ _
  · intro reg member
    have pcOther : ¬ ((Register.PC == reg) = true) := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have returnOther : ¬ ((Register.x5 == reg) = true) := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change ((state.regs.insert Register.x5 execution.result).insert Register.PC (execution.nextPc pc)).get? reg = _
    rw [Std.ExtDHashMap.get?_insert, dif_neg pcOther, Std.ExtDHashMap.get?_insert, dif_neg returnOther]

/-- Concrete syscall execution authenticates architectural observations and preserves all other
registers, configuration, and protected bytes. The RAM write itself remains in the semantic step. -/
theorem hostStep_effect {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : Machine.CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall event) target) :
    event.MatchesStates source.sail target.sail ∧
      (∀ index : BitVec 5, index ≠ 5 → target.sail.get_reg? index = source.sail.get_reg? index) ∧
      (SailConfigured source.sail → SailConfigured target.sail) ∧
      (∀ address, policy.memory.readOnly address = true → target.sail.mem.get? address = source.sail.mem.get? address) := by
  cases step with
  | syscall success =>
    obtain ⟨pc, execution, atPc, _, ran, _, targetEq, eventEq⟩ := HostState.step_observations success
    rw [targetEq, eventEq]
    exact ⟨execution.matchesStates ran atPc _, execution.register_frame source.sail pc,
      host_apply_configured execution source.sail pc, execution.preserves_readOnly ran pc⟩

/-- Preserving the image's protected bytes preserves the whole committed instruction memory. -/
theorem romLoaded_of_readOnly (image : ProgramImage) (valid : image.Valid) {source target : SailState}
    (preserved : ∀ address, image.readOnly address = true → target.mem.get? address = source.mem.get? address)
    (loaded : RomLoaded (image.toGuestProgram valid) source) : RomLoaded (image.toGuestProgram valid) target := by
  intro pc word fetched index
  have readonly : image.readOnly (pc.toNat + index) = true := by
    obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
    have member : entry ∈ image.rom := List.mem_of_find?_eq_some found
    have atPc : entry.1 = pc := by simpa using List.find?_some found
    apply (image.readOnly_iff _).mpr
    exact ⟨entry, member, by rw [atPc]; omega, by rw [atPc]; have := index.isLt; omega⟩
  exact (preserved _ readonly).trans (loaded pc word fetched index)

end SP1Clean.Soundness
