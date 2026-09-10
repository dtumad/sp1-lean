import SP1Clean.Soundness.NativeCoreState
import SP1Clean.Soundness.StateChronology

/-! # Clock ordering of the authenticated native core

Raw constraints and channel balance order every active ordinary, HALT, and syscall row between
the public endpoints. The physical StateBump rows supply canonicalization, and cancel internally.
The order retains every occurrence, including arbitrarily interleaved syscall rows.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The constrained event widths, in SP1 bus ticks. -/
def ExecutionRow.duration : ExecutionRow p → ℕ
  | .instruction _ => 8
  | .halt _ | .syscall _ => 264

/-- The State edge after canonical re-limbing. -/
noncomputable def ExecutionRow.canonEdge (data : ProverData (ZMod p)) (row : ExecutionRow p) :=
  (canonState (row.edge data).1, canonState (row.edge data).2)

omit [Fact (2 ^ 25 < p)] in
private theorem activeSystemRows_member {α : Type} (table : Table (ZMod p))
    (decode : Table (ZMod p) → Array (ZMod p) → α) (gate : α → ZMod p)
    {row : α} (member : row ∈ activeSystemRows table decode gate) :
    ∃ physical ∈ table.table, decode table physical = row ∧ gate row = 1 := by
  obtain ⟨mapped, active⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact ⟨physical, physicalMem, rfl, of_decide_eq_true active⟩

private theorem syscall_halt_binary (table : Table (ZMod p))
    (component : table.component = ⟨SyscallInstrsChip.circuit⟩) (constraints : table.Constraints)
    {physical : Array (ZMod p)} (member : physical ∈ table.table) :
    (syscallInstrsRow table physical).is_halt = 0 ∨ (syscallInstrsRow table physical).is_halt = 1 := by
  have checked := constraints physical member
  rw [component] at checked
  have binary := SyscallInstrsChip.haltSelectorBinary_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints SyscallInstrsChip.circuit _ checked)
  simpa only [syscallInstrsRow_eq, circuit_norm] using binary

private theorem halt_advancing (row : HaltChip.Inputs (ZMod p))
    (bounds : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8) :
    StateChronology.Advancing (HaltChip.statePulledMessage row, HaltChip.statePushedMessage row) ∧
      StateMsg.timeNat (HaltChip.statePushedMessage row) =
        StateMsg.timeNat (HaltChip.statePulledMessage row) + 264 := by
  have step : StateMsg.timeNat (HaltChip.statePushedMessage row) =
      StateMsg.timeNat (HaltChip.statePulledMessage row) + 264 :=
    TimeExtraction.clkNat_add_syscall_of_cpuState_bounds _ _ _ bounds.1 bounds.2
  refine ⟨⟨?_, rfl, Or.inr ?_⟩, step⟩
  · dsimp only
    rw [step]; omega
  · change (0 : ZMod p).val < 2 ^ 16 ∧ (0 : ZMod p).val < 2 ^ 16
    simp

private theorem syscall_advancing (row : SyscallInstrsChip.Inputs (ZMod p))
    (bounds : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
      row.state.clk_16_24.val < 2 ^ 8)
    (binary : row.is_halt = 0 ∨ row.is_halt = 1) (real : row.is_real = 1)
    (arm : (row.is_halt = 1 → row.next_pc[0] = 1 ∧ row.next_pc[1] = 0 ∧ row.next_pc[2] = 0) ∧
      (row.is_real = 1 → row.is_halt = 0 → row.next_pc[0] = row.state.pc[0] + 4 ∧
        row.next_pc[1] = row.state.pc[1] ∧ row.next_pc[2] = row.state.pc[2])) :
    StateChronology.Advancing (SyscallInstrsChip.statePulledMessage row, SyscallInstrsChip.statePushedMessage row) ∧
      StateMsg.timeNat (SyscallInstrsChip.statePushedMessage row) =
        StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 264 := by
  have step : StateMsg.timeNat (SyscallInstrsChip.statePushedMessage row) =
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 264 :=
    TimeExtraction.clkNat_add_syscall_of_cpuState_bounds _ _ _ bounds.1 bounds.2
  refine ⟨⟨?_, rfl, ?_⟩, step⟩
  · dsimp only
    rw [step]; omega
  · rcases binary with inactive | active
    · exact Or.inl (arm.2 real inactive).2
    · change (_ ∧ _) ∨ row.next_pc[1].val < 2 ^ 16 ∧ row.next_pc[2].val < 2 ^ 16
      right
      rw [(arm.1 active).2.1, (arm.1 active).2.2]
      simp

private theorem instructionRows_advancing {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p} (member : row ∈ activeInstructionRows witness) :
    StateChronology.Advancing ((ExecutionRow.instruction row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.instruction row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.instruction row).edge witness.data).1 + (ExecutionRow.instruction row).duration := by
  obtain ⟨decodedMem, real⟩ := List.mem_filter.mp member
  have active := of_decide_eq_true real
  have byte := (instructionRows_finished_guarantees witness constraints balanced decodedMem).1
  have step := row.stateTimeStep_of_byteGuarantees witness.data (witness.tables.drop 7) decodedMem byte active
  refine ⟨⟨?_, rfl, ?_⟩, step⟩
  · change StateMsg.timeNat (decodedStateEdge witness.data row).1 <
      StateMsg.timeNat (decodedStateEdge witness.data row).2
    rw [step]; omega
  · exact supportedChip_statePcClassShape row.chip (mem_chip_of_mem_decodeInstructionTables decodedMem)
      witness.data row.physical byte active

private theorem haltRows_advancing {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 2) haltRow (·.is_real)) :
    StateChronology.Advancing ((ExecutionRow.halt row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.halt row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.halt row).edge witness.data).1 + (ExecutionRow.halt row).duration := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact halt_advancing _ (haltRow_cpuState_bounds_of_component _ (systemTable_component witness 2)
    (finishedChannel_guarantees image witness constraints balanced _ (systemTable_mem witness 2)).1 physicalMem real)

private theorem syscallRows_advancing {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : row ∈ activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real)) :
    StateChronology.Advancing ((ExecutionRow.syscall row).edge witness.data) ∧
      StateMsg.timeNat ((ExecutionRow.syscall row).edge witness.data).2 =
        StateMsg.timeNat ((ExecutionRow.syscall row).edge witness.data).1 + (ExecutionRow.syscall row).duration := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact syscall_advancing _ (syscallInstrsRow_cpuState_bounds_of_component _ (systemTable_component witness 3)
    (finishedChannel_guarantees image witness constraints balanced _ (systemTable_mem witness 3)).1 physicalMem real)
    (syscall_halt_binary _ (systemTable_component witness 3) (systemTable_constraints witness constraints 3) physicalMem)
    real (syscallInstrsRow_pcArm_spec_of_component _ (systemTable_component witness 3)
      (systemTable_constraints witness constraints 3) physicalMem)

/-- Clock progress and the PC preservation/range-check dichotomy come from each physical row. -/
theorem executionRows_advancing {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Advancing (row.edge witness.data) ∧
      StateMsg.timeNat (row.edge witness.data).2 =
        StateMsg.timeNat (row.edge witness.data).1 + row.duration := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, member, rfl⟩ | ⟨halt, member, rfl⟩) | ⟨syscall, member, rfl⟩
  · exact instructionRows_advancing witness constraints balanced member
  · exact haltRows_advancing witness constraints balanced member
  · exact syscallRows_advancing witness constraints balanced member

private theorem stateBumps_spec {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : StateBumpChip.Inputs (ZMod p)} (member : row ∈ stateBumps witness) :
    StateBumpChip.Spec row ∧ row.is_real = 1 := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  exact ⟨stateBumpTable_spec_of_component _ (systemTable_component witness 1)
    (systemTable_constraints witness constraints 1)
    (finishedChannel_guarantees image witness constraints balanced _ (systemTable_mem witness 1)).1 _ physicalMem, real⟩

/-- Both endpoints of every active event have the bounds needed for semantic canonicalization. -/
theorem executionRows_good {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : ExecutionRow p} (member : row ∈ executionRows witness) :
    StateChronology.Good (row.edge witness.data).1 ∧ StateChronology.Good (row.edge witness.data).2 := by
  have bounds := (public_boot witness constraints balanced).1
  have initial := initialBoundaryStateMessage_bounds witness.publicInput bounds
  have final := finalBoundaryStateMessage_bounds witness.publicInput bounds
  exact (StateChronology.good_and_bumps_cancel _ _ _ _ _ (state_endpointBalanced witness constraints balanced)
    ⟨initial.1, initial.2.2.2⟩ ⟨final.1, final.2.2.2⟩
    (fun _ member => (executionRows_advancing witness constraints balanced member).1)
    (fun _ member => stateBumps_spec witness constraints balanced member)).1 row member

/-- Constraints and balance construct an exhaustive ordering of the complete mixed inventory.
No ordering, canonicalization, or system-row inactivity premise is supplied by the caller. -/
theorem executionRows_ordered {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ ordered : List (ExecutionRow p), ordered.Perm (executionRows witness) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered := by
  have bounds := (public_boot witness constraints balanced).1
  have initial := initialBoundaryStateMessage_bounds witness.publicInput bounds
  have final := finalBoundaryStateMessage_bounds witness.publicInput bounds
  obtain ⟨ordered, walk, exhaustive⟩ := StateChronology.exhaustiveTrail _ _ _ _ _
    (state_endpointBalanced witness constraints balanced)
    ⟨initial.1, initial.2.2.2⟩ ⟨final.1, final.2.2.2⟩
    (fun _ member => (executionRows_advancing witness constraints balanced member).1)
    (fun _ member => stateBumps_spec witness constraints balanced member)
  rw [canonState_eq_self initial.2.1 initial.2.2.1 initial.2.2.2.1,
    canonState_eq_self final.2.1 final.2.2.1 final.2.2.2.1] at walk
  exact ⟨ordered, exhaustive, walk⟩

/-- Every event in an exhaustive State walk keeps the boot clock residue and its exact duration. -/
theorem ordered_rows_timing {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (ordered : List (ExecutionRow p)) (exhaustive : ordered.Perm (executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) ordered) :
    ∀ row ∈ ordered,
      StateMsg.timeNat (row.edge witness.data).1 % 8 =
        StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) % 8 ∧
      StateMsg.timeNat (row.edge witness.data).2 = StateMsg.timeNat (row.edge witness.data).1 + row.duration := by
  have steps : ∀ row ∈ ordered,
      StateMsg.timeNat (row.canonEdge witness.data).2 =
        StateMsg.timeNat (row.canonEdge witness.data).1 + row.duration := by
    intro row member
    have good := executionRows_good witness constraints balanced (exhaustive.mem_iff.mp member)
    dsimp only [ExecutionRow.canonEdge]
    rw [timeNat_canonState good.1.1, timeNat_canonState good.2.1]
    exact (executionRows_advancing witness constraints balanced (exhaustive.mem_iff.mp member)).2
  have aligned := statePullAlign8_of_durations (ExecutionRow.canonEdge witness.data) ExecutionRow.duration walk
    (fun row _ => by cases row <;> norm_num [ExecutionRow.duration]) steps
  intro row member
  have good := executionRows_good witness constraints balanced (exhaustive.mem_iff.mp member)
  have align := aligned row member
  dsimp only [ExecutionRow.canonEdge] at align
  rw [timeNat_canonState good.1.1] at align
  exact ⟨align, (executionRows_advancing witness constraints balanced (exhaustive.mem_iff.mp member)).2⟩

end SP1Clean.Soundness.NativeCore
