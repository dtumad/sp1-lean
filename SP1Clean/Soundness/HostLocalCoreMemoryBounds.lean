import SP1Clean.Soundness.HostLocalCoreMemory
import SP1Clean.Soundness.LocalCoreTouches

/-! # Low-clock bounds from the full host Memory ledger

Original instruction and refresh pushes use constraints, Byte guarantees, and Program balance.
The wrapper's extra x12 push uses the same CPU clock checks. Auxiliary pushes remain in the
physical ledger and supply their own local clock bounds. Full record conservation then transfers
these bounds to predecessors; no instruction-only Memory balance is asserted.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem wrapper_extra_bound (table : Table (ZMod p))
    (component : table.component = HostCallLedger.producer)
    (bytes : table.ChannelGuarantees byteChannel.toRaw)
    (physical : Array (ZMod p)) (member : physical ∈ table.table)
    (real : (HostCallLedger.input (table.environment physical)).instruction.is_real = 1) :
    MemoryMsg.ClkBound (HostCallProjection.extraRead (table.environment physical)).pushed := by
  have same : (HostCallLedger.input (table.environment physical)).instruction =
      syscallInstrsRow (table.withComponent HostCallProjection.original) physical :=
    HostCallProjection.input_original _
  have originalByte : (table.withComponent HostCallProjection.original).ChannelGuarantees byteChannel.toRaw := by
    apply table.withComponent_channelGuarantees_of
    · rw [component]
      exact HostCallProjection.byte_guarantees
    · exact bytes
  have originalReal := (congrArg (fun row : SyscallInstrsChip.Inputs (ZMod p) => row.is_real) same).symm.trans real
  have bounds := syscallInstrsRow_cpuState_bounds_of_component
    (table.withComponent HostCallProjection.original) rfl originalByte member originalReal
  rw [← same] at bounds
  exact MemoryMsg.clkBound_of_cpuState_bounds _ _ 1 1 (ZMod.val_one _) (by decide) bounds.1 bounds.2

private theorem wrapper_push_bound (table : Table (ZMod p))
    (component : table.component = HostCallLedger.producer)
    (constraints : table.Constraints) (bytes : table.ChannelGuarantees byteChannel.toRaw)
    (original : ∀ message ∈ producedMessages
      (typedTableInteractionsWith (table.withComponent HostCallProjection.original) memoryChannel),
      MemoryMsg.ClkBound message) :
    ∀ message ∈ producedMessages (typedTableInteractionsWith table memoryChannel),
      MemoryMsg.ClkBound message := by
  intro message member
  rw [typedTableInteractionsWith, producedMessages_flatMap] at member
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp member
  have checked := constraints physical physicalMem
  rw [component] at checked emitted
  rw [wrapper_memory_interactions _ checked, producedMessages_append] at emitted
  rcases List.mem_append.mp emitted with old | extra
  · apply original
    rw [typedTableInteractionsWith, producedMessages_flatMap]
    exact List.mem_flatMap.mpr ⟨physical, physicalMem, old⟩
  · have binary := HostCallLedger.binary_of_constraints (table.environment physical) checked
    have flag := HostCallChip.writeFlag_binary (HostCallLedger.input (table.environment physical)).instruction.op_a_memory.prev_value
    have zero : signedVal (0 : ZMod p) = 0 := by simp [signedVal]
    rcases binary with inactive | real
    · simp [producedMessages, HostCallProjection.extraRead, HostCallChip.Inputs.read, inactive,
        zero] at extra
    · have bound := wrapper_extra_bound table component bytes physical physicalMem real
      rcases flag with disabled | enabled
      · simp [producedMessages, HostCallProjection.extraRead, HostCallChip.Inputs.read, disabled,
          zero] at extra
      · have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
        have gate : (HostCallProjection.extraRead (table.environment physical)).is_real = 1 := by
          simp only [HostCallProjection.extraRead, HostCallChip.Inputs.read, real, enabled, mul_one]
        have pos : signedVal (1 : ZMod p) = 1 := by
          rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
          norm_num
        have neg : signedVal (-1 : ZMod p) = -1 := by
          rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
          norm_num
        simp [producedMessages, gate, pos, neg] at extra
        exact extra ▸ bound

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

private theorem original_table_bound (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (bounded : ∀ message ∈ producedMessages (LocalCore.memoryInterior (localWitness witness)),
      MemoryMsg.ClkBound message) (index : Fin 59) (interior : 6 ≤ index.val) :
    ∀ message ∈ producedMessages (typedTableInteractionsWith
      ((localWitness witness).tables[index.val]'(by
        rw [← (localWitness witness).same_length]; change index.val < (LocalCore.tables image source).length
        rw [LocalCore.tables_length]; exact index.isLt)) memoryChannel),
      MemoryMsg.ClkBound message := by
  intro message member
  apply bounded
  rw [LocalCore.memoryInterior, producedMessages_flatMap]
  refine List.mem_flatMap.mpr ⟨_, ?_, member⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨index.val - 6, ?_, ?_⟩
  · simp only [List.length_drop, ← (localWitness witness).same_length,
      LocalCore.ensemble, LocalCore.tables_length]
    omega
  · simp only [List.getElem_drop, Nat.add_sub_cancel' interior]

/-- Every physical interior push has a bounded low clock. The original rows, WRITE's x12
read-back, and the actual auxiliary pushes are all retained; Memory balance is not a premise. -/
theorem memoryInterior_push_bound (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    (originalBytes : ∀ table ∈ (localWitness witness).allTables, table.ChannelGuarantees byteChannel.toRaw)
    (program : (localWitness witness).BalancedChannel programChannel.toRaw)
    (extra : ∀ table ∈ auxiliaryTables witness,
      ∀ message ∈ producedMessages (typedTableInteractionsWith table memoryChannel), MemoryMsg.ClkBound message) :
    ∀ message ∈ producedMessages (memoryInterior witness), MemoryMsg.ClkBound message := by
  have original := LocalCore.memoryInterior_push_bound valid (localWitness witness)
    (localWitness_constraints witness constraints) originalBytes program
  intro message member
  rw [memoryInterior, producedMessages_flatMap] at member
  obtain ⟨table, tableMem, emitted⟩ := List.mem_flatMap.mp member
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp tableMem
  have bound : i + 6 < witness.tables.length := by simp only [List.length_drop] at hi; omega
  simp only [List.getElem_drop, Nat.add_comm 6] at emitted
  have present := witness.mem_allTables_of_mem_tables (List.getElem_mem (l := witness.tables) (n := i + 6) bound)
  by_cases old : i + 6 < 59
  · have bounded := original_table_bound witness original ⟨i + 6, old⟩ (by change 6 ≤ i + 6; omega)
    rw [localWitness_table] at bounded
    by_cases wrapper : i + 6 = 58
    · have component : (witness.tables[i + 6]).component = HostCallLedger.producer := by
        rw [← witness.same_circuits]
        change (tables image source auxiliary)[i + 6]'(by rw [tables_length]; omega) = _
        rw [core_component image source auxiliary ⟨i + 6, old⟩, if_pos wrapper.symm]
      have originalComponent : (LocalCore.tables (p := p) image source)[i + 6]'(by
          rw [LocalCore.tables_length]; exact old) = HostCallProjection.original := by simp only [wrapper]; rfl
      rw [originalComponent] at bounded
      exact wrapper_push_bound _ component (constraints _ present) (bytes _ present) bounded message emitted
    · have same : typedTableInteractionsWith
          ((witness.tables[i + 6]).withComponent ((LocalCore.tables image source)[i + 6]'(by
            rw [LocalCore.tables_length]; exact old))) memoryChannel =
          typedTableInteractionsWith (witness.tables[i + 6]) memoryChannel := by
        apply List.map_injective_iff.mpr TypedInteraction.raw_injective
        simp only [typedTableInteractionsWith_raw]
        apply Table.withComponent_interactions
        rw [← witness.same_circuits]
        change _ = ((tables image source auxiliary)[i + 6]'(by rw [tables_length]; omega)).operations.interactionsWith _
        rw [core_component image source auxiliary ⟨i + 6, old⟩, if_neg (Ne.symm wrapper)]
        exact ((ProtectedLocalCore.component_projection (p := p) image source ⟨i + 6, old⟩).2.2
          memoryChannel.toRaw (by simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw])).symm
      rw [same] at bounded
      exact bounded message emitted
  · by_cases permission : i + 6 = 59
    · have component : (witness.tables[i + 6]).component = ⟨WritePermissionProvider.circuit image⟩ := by
        rw [← witness.same_circuits]
        change (tables image source auxiliary)[i + 6]'(by rw [tables_length]; omega) = _
        simp only [permission]
        simp only [tables]
        rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; decide),
          List.getElem_set_ne (by decide)]
        rfl
      have silent : (witness.tables[i + 6]).interactionsWith memoryChannel.toRaw = [] := by
        apply Table.interactionsWith_nil_of_channel_not_mem
        rw [component]
        change memoryChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
        simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
      have typed : typedTableInteractionsWith (witness.tables[i + 6]) memoryChannel = [] := by
        apply (List.map_eq_nil_iff (f := TypedInteraction.raw)).mp
        rwa [typedTableInteractionsWith_raw]
      simp [typed, producedMessages] at emitted
    · apply extra _ ?_ message emitted
      apply List.mem_iff_getElem.mpr
      refine ⟨i + 6 - 60, ?_, ?_⟩
      · simp only [auxiliaryTables, List.length_drop]; omega
      · simp only [auxiliaryTables, List.getElem_drop, Nat.add_sub_cancel' (show 60 ≤ i + 6 by omega)]

end SP1Clean.Soundness.HostLocalCore
