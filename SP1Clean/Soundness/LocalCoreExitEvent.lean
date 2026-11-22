import SP1Clean.Soundness.LocalCoreExit
import SP1Clean.Soundness.CoreExecutionEvents

/-! # Recovering the source of a nonzero public Exit
The sole emitted Exit can come from HALT padding, a real legacy HALT, or a selected syscall
instruction. Padding emits zero. Both remaining cases contribute a parked event to the
physical CPU inventory.
-/

namespace SP1Clean.Soundness.LocalCore
open Circuit Air.Flat Channels Semantics NativeCore
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance exitEventClockBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem real_of_halt (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (shallow : ConstraintsHold.Shallow env ((SyscallInstrsChip.main input).operations offset))
    (selected : Expression.eval env input.is_halt = 1) : Expression.eval env input.is_real = 1 := by
  have pad : (Expression.eval env input.is_real - 1) * Expression.eval env input.is_halt = 0 := by
    simpa only [circuit_norm] using shallow.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [selected, mul_one] at pad
  exact sub_eq_zero.mp pad

local instance exitEventDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

variable [Fact (2 ^ 25 < p)]

/-- A nonzero public Exit selects a real parked syscall in the physical row inventory. -/
theorem parked_of_nonzero_exit {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel exitChannel.toRaw)
    (nonzero : witness.publicInput.exit_code ≠ 0) :
    ∃ call, Machine.ExecutionEvent.syscall call ∈ (executionRows witness).map ExecutionRow.event ∧
      call.nextPc = Machine.haltPc := by
  have emitted := exit_messages witness constraints balanced
  have mem : (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) ∈
      ((exitProducers witness).filter (fun e => decide (e.1 = 1))).map Prod.snd := by
    rw [emitted]; exact List.mem_singleton_self _
  obtain ⟨⟨gate, msg⟩, selected, rfl⟩ := List.mem_map.mp mem
  obtain ⟨producer, active⟩ := List.mem_filter.mp selected
  have one : gate = 1 := of_decide_eq_true active
  subst gate
  rcases List.mem_append.mp producer with legacy | syscall
  · obtain ⟨physical, present, emitted⟩ := List.mem_flatMap.mp legacy
    let row := haltRow witness.data physical
    rcases List.mem_cons.mp emitted with real | pad
    · have selected : row.is_real = 1 := (congrArg Prod.fst real).symm
      have member : ExecutionRow.halt row ∈ executionRows witness := by
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨row, List.mem_filter.mpr ⟨List.mem_map_of_mem (f := haltRow witness.data) present, by simpa using selected⟩, rfl⟩
      exact ⟨_, List.mem_map_of_mem (f := ExecutionRow.event) member, rfl⟩
    · have eq := List.mem_singleton.mp pad
      exact (nonzero (congrArg (fun e : ZMod p × ExitMsg (ZMod p) => e.2.value) eq)).elim
  · obtain ⟨physical, present, eq⟩ := List.mem_map.mp syscall
    let table := systemTable witness 3
    let row := syscallInstrsRow witness.data physical
    have selected : row.is_halt = 1 := congrArg Prod.fst eq
    have checked := systemTable_constraints witness constraints 3 physical present
    rw [systemTable_component witness 3] at checked
    have shallow := shallowConstraints_of_componentConstraints SyscallInstrsChip.circuit _ checked
    have real : row.is_real = 1 := by
      have select := real_of_halt _ _ _ shallow
      simp only [row, syscallInstrsRow_eq, circuit_norm, Table.environment, Environment.fromArray] at select selected ⊢
      exact select selected
    have member : ExecutionRow.syscall row ∈ executionRows witness := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨row, List.mem_filter.mpr ⟨List.mem_map_of_mem (f := syscallInstrsRow witness.data) present,
        by simpa using real⟩, rfl⟩
    have ⟨pc₀, pc₁, pc₂⟩ := (syscallInstrsRow_pcArm_spec_of_component table witness.data
      (systemTable_component witness 3) (witness.same_data _ (systemTable_mem witness 3))
      (systemTable_constraints witness constraints 3) present).1 selected
    refine ⟨_, List.mem_map_of_mem (f := ExecutionRow.event) member, ?_⟩
    rw [nextPc_syscallEventOfRow, pc₀, pc₁, pc₂, ZMod.val_one, ZMod.val_zero]
    rfl
end SP1Clean.Soundness.LocalCore
