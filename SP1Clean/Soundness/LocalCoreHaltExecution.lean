import SP1Clean.Soundness.LocalCoreTransport
import SP1Clean.Soundness.WalkTimeline
import SP1Clean.Soundness.CoreExecutionTrajectory
import SP1Clean.Soundness.CoreInstructionExecution
import SP1Clean.Soundness.CoreHaltExecution

/-! # Stateful HALT grounding for local shards

The actual Program ledger authenticates ECALL. HALT's own assertions and incoming Memory
currency then determine the complete host transition on the carrier's paired replay. This closes
the HALT step/frame obligation without a boot assumption or a caller-supplied HALT successor.
ROM preservation and active SyscallInstrs effects remain explicit obligations.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow haltEventOfRow)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem halt_member {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) :
    ∃ physical ∈ (systemTable witness 2).table,
      haltRow witness.data physical = row ∧ row.is_real = 1 := by
  have active : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real) := by
    simpa [executionRows] using member
  exact NativeCore.activeSystemRows_member _ _ _ active

/-- Every active HALT fetch belongs to the checked image, by the actual Program balance. -/
theorem halt_program_committed_of_balance {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg (HaltChip.programMessage row)) := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := halt_member member
  let row := haltRow witness.data physical
  let message := HaltChip.programMessage row
  let interaction := programChannel.pulledIfValue row.is_real message
  have emitted : interaction ∈ witness.interactionsWith programChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨systemTable witness 2, systemTable_mem witness 2, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    have shared : (systemTable witness 2).data = witness.data :=
      witness.same_data _ (systemTable_mem witness 2)
    rw [Table.environment, shared, ← typedInteractionValuesWith_raw,
      haltRow_typedProgram_of_component _ witness.data (systemTable_component witness 2)]
    exact List.mem_cons_self
  exact program_pull_committed_of_balance valid witness constraints balanced message interaction emitted
    (by exact ⟨rfl, real⟩) rfl

/-- HALT's own assertions fix the zero code and three zero exit limbs; Byte fixes the clock. -/
theorem haltRows_staticFacts_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees byteChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Word.toBitVec64 row.x5_memory.prev_value = 0 ∧
      (row.x10_memory.prev_value[1] = 0 ∧ row.x10_memory.prev_value[2] = 0 ∧ row.x10_memory.prev_value[3] = 0) ∧
      (((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8) := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := halt_member member
  have checked := systemTable_constraints witness constraints 2 physical physicalMem
  have shared : (systemTable witness 2).data = witness.data :=
    witness.same_data _ (systemTable_mem witness 2)
  rw [Table.environment, shared, systemTable_component witness 2] at checked
  have realEval : Expression.eval (Environment.fromArray physical witness.data)
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p)).is_real = 1 := by
    simpa only [haltRow_eq, circuit_norm] using real
  have shallow := shallowConstraints_of_componentConstraints HaltChip.circuit _ checked
  have zero := HaltChip.codeZero_of_shallow _ _ _ shallow realEval
  have high := HaltChip.exitHighZero_of_shallow _ _ _ shallow realEval
  refine ⟨?_, ?_, haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    (witness.same_data _ (systemTable_mem witness 2))
    (bytes _ (systemTable_mem witness 2))
    physicalMem real⟩
  · simpa only [haltRow_eq] using zero
  · simpa only [haltRow_eq] using high

end SP1Clean.Soundness.LocalCore
