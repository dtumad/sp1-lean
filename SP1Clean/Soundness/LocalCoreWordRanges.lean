import SP1Clean.Soundness.LocalCoreTouches

/-! # Row-local word ranges from the physical Memory and Byte ledgers

Ordinary components derive each push requirement by their checked bundled circuit.
ECALL independently range-checks the fresh x5 result. Its two remaining pushes and
all legacy HALT pushes carry original register words.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Channels Semantics NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] {image : ProgramImage} {source : ExecutionSnapshot}

local instance wordRangeGt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance wordRangeGt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The decoded instruction inherits its original component constraints, Byte and Program guarantees. -/
theorem instruction_staticInputs
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (byte : ∀ table ∈ witness.tables, table.ChannelGuarantees byteChannel.toRaw)
    (program : ∀ table ∈ witness.tables, table.ChannelGuarantees programChannel.toRaw)
    {row : DecodedInstructionRow p} (member : row ∈ LocalCore.instructionRows witness) :
    DecodedRowStaticInputs row witness.data :=
  ⟨mem_chip_of_mem_decodeInstructionTables member,
    LocalCore.instructionRows_constraints witness constraints row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table member => witness.same_data table (LocalCore.instructionTables_mem witness member))
      (fun table tableMem => byte table (LocalCore.instructionTables_mem witness tableMem)) row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table member => witness.same_data table (LocalCore.instructionTables_mem witness member))
      (fun table tableMem => program table (LocalCore.instructionTables_mem witness tableMem)) row member⟩

/-- Every mixed CPU row preserves word well-formedness when its original Memory inputs
satisfy their structural guarantee. No Memory input is assumed to agree with Sail. -/
theorem executionRows_word_ranges (valid : image.Valid) (w : EnsembleWitness (ensemble (p := p) image source))
    (checked : w.Constraints) (bytes : ∀ table ∈ w.tables, table.ChannelGuarantees byteChannel.toRaw)
    (program : w.BalancedChannel programChannel.toRaw) {row : ExecutionRow p} (member : row ∈ executionRows w)
    (incoming : ∀ mp ∈ (row.facts w.data).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    ∀ m ∈ (row.facts w.data).memPushes, MemoryMsg.isU64 m := by
  simp only [executionRows, List.mem_append, List.mem_map] at member
  rcases member with (⟨decoded, active, rfl⟩ | ⟨halt, _, rfl⟩) | ⟨call, active, rfl⟩
  · obtain ⟨included, gate⟩ := List.mem_filter.mp active
    have facts := instruction_staticInputs w checked bytes (program_guarantees_of_balance image source w checked program).2 included
    have real := of_decide_eq_true gate
    have committed := instructionRows_program_committed_of_balance valid w checked program included real
    have decode := committed.decoded_of_opcode_ne (supportedChip_fetchDiscriminantShape decoded.chip facts.registered w.data decoded.physical facts.constraints facts.byte real)
    have inputs := decoded.memoryChannelGuarantees_of_pullCurrency w.data incoming
    have assumptions := (supportedChip_groundingContracts decoded.chip facts.registered).assumptionsLocal w.data decoded rfl facts real _ decode inputs
    have outputs := producedMemoryMessages_isU64_of_fullRequirements decoded w.data (facts.fullRequirements ⟨assumptions, inputs⟩)
    exact outputs
  · intro m inside
    obtain ⟨pair, used, rfl⟩ := List.mem_map.mp inside
    have old := (incoming _ (List.mem_map_of_mem (f := fun p => (p.1, StateMsg.timeNat (HaltChip.statePulledMessage halt))) used)).1
    simp only [HaltChip.memoryPairs, List.mem_cons, List.not_mem_nil, or_false] at used
    rcases used with rfl | rfl | rfl <;> exact old
  · obtain ⟨mapped, real⟩ := List.mem_filter.mp active
    obtain ⟨physical, used, rfl⟩ := List.mem_map.mp mapped
    have result := syscallInstrsRow_opAValue_isU64_of_component _ w.data (systemTable_component w 3)
      (w.same_data _ (systemTable_mem w 3)) (bytes _ (systemTable_mem w 3)) used (of_decide_eq_true real)
    have b := (incoming _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
    have c := (incoming _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).1
    intro m inside
    change m ∈ (syscallRowFacts _).memPushes at inside
    simp only [syscallRowFacts, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl
    · exact result
    · exact b
    · exact c

end SP1Clean.Soundness.LocalCore
