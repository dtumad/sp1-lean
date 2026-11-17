import SP1Clean.Soundness.SystemMemoryRows
import SP1Clean.Soundness.TypedTimeContracts

/-! # Component-local syscall inputs

Physical constraints and finished Byte/Program guarantees supply the syscall contract. The three
Memory pulls receive their value and clock bounds from the grounding engine's incoming currency.
These lemmas apply to any table carrying the syscall component, independently of ensemble layout.
They do not supply host effects or restrict the complete syscall register to a supported code.
-/

open LeanRV64D

namespace SP1Clean.Soundness

open SP1Clean.Machine SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance syscallInputs_fact24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallInputs_fact17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Rebuild the row's Memory guarantee from its three incoming records. -/
theorem syscallInstrsRow_memoryGuarantees_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation })
    (_constraints : table.Constraints)
    {row : Array (ZMod p)} (_rowMem : row ∈ table.table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    table.component.operations.ChannelGuarantees memoryChannel.toRaw
      (Environment.fromArray row data) := by
  refine channelGuarantees_of_consumedMessages _ memoryChannel _ fun msg msgMem => ?_
  rw [syscallInstrsRow_typedMemory_of_component table data component, consumedMessages, List.mem_map] at msgMem
  obtain ⟨i, iMem, rfl⟩ := msgMem
  have iMem := List.mem_filter.mp iMem
  simp only [decide_eq_true_eq] at iMem
  obtain ⟨iList, iPull⟩ := iMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at iList
  rcases iList with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_a_memory
      (syscallInstrsRow data row).op_a,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row))) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_self
  · exact Channel.Direction.noConfusion iPull.1
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_b_memory
      (syscallInstrsRow data row).op_b,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row)) + 3) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact Channel.Direction.noConfusion iPull.1
  · rw [TypedInteraction.pulledIfValue_message]
    refine currency (SyscallInstrsChip.memPulledMessage
      (syscallInstrsRow data row)
      (syscallInstrsRow data row).op_c_memory
      (syscallInstrsRow data row).op_c,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
        (syscallInstrsRow data row)) + 2) ?_
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Channel.Direction.noConfusion iPull.1

/-- Read the committed ECALL's local Program guarantee at one active physical row. -/
theorem syscallInstrsRow_programRowSpec_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation })
    (sameData : table.data = data)
    (program : table.ChannelGuarantees programChannel.toRaw)
    {row : Array (ZMod p)} (rowMem : row ∈ table.table)
    (real : (syscallInstrsRow data row).is_real = 1) :
    Channels.ProgramMsg.RowSpec (SyscallInstrsChip.programMessage (syscallInstrsRow data row)) := by
  have programGuarantees := program row rowMem
  have guarantee := TypedInteraction.guarantee_of_channelGuarantees
    table.component.operations programChannel
    (Environment.fromArray row data)
    (TypedInteraction.pulledIfValue programChannel (syscallInstrsRow data row).is_real
      (SyscallInstrsChip.programMessage (syscallInstrsRow data row)))
    (by rw [syscallInstrsRow_typedProgram_of_component table data component]; exact List.mem_cons_self)
    (by simpa only [Table.environment, sameData] using programGuarantees)
    ⟨rfl, real⟩
  simpa only [TypedInteraction.pulledIfValue_message, programChannel] using guarantee

/-- The complete syscall contract and well-formed operand words, derived within incoming currency. -/
theorem syscallInstrsRow_contract_of_component
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = { circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation })
    (sameData : table.data = data)
    (constraints : table.Constraints)
    (byte : table.ChannelGuarantees byteChannel.toRaw)
    (program : table.ChannelGuarantees programChannel.toRaw)
    {row : Array (ZMod p)} (member : row ∈ table.table)
    (currency : ∀ mp ∈ (syscallRowFacts (syscallInstrsRow data row)).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (syscallInstrsRow data row) ∧
      SyscallInstrsChip.PulledFacts (syscallInstrsRow data row) := by
  refine ⟨syscallInstrsRow_spec_of_component table data component sameData constraints byte program
    (syscallInstrsRow_memoryGuarantees_of_component table data component constraints member currency) member, ?_⟩
  intro real
  obtain ⟨a, b, c⟩ := syscallRowFacts_currency_split _ currency
  exact SyscallInstrsChip.pulledFacts_of_buses _
    (syscallInstrsRow_programRowSpec_of_component table data component sameData program member real) a b c
    (syscallInstrsRow_opAValue_isU64_of_component table data component sameData byte member real) real

end SP1Clean.Soundness
