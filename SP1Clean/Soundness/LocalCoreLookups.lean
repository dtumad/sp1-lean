import SP1Clean.Soundness.LocalCoreEnsemble

/-! # Static lookup dependencies of the local execution assembly

The physical inventory's only lookup keys authenticate the source registers, source memory,
program ROM and Clean's byte XOR table. This follows from circuit-owned metadata and the typed
instruction registry, without importing Rust oracles. Individual projections retain repeated
lookups; the subset theorem below is only a dependency bound for canonical-data transport.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

attribute [local circuit_norm]
  SnapshotMemoryEnsemble.registerView SnapshotMemoryEnsemble.ramView
  SnapshotMemoryEnsemble.terminalView
  FinalMemoryEnsemble.inventory FinalMemoryEnsemble.viewFor
  FinalMemoryEnsemble.registerView FinalMemoryEnsemble.ramView
  OrderedMemoryEnsemble.Inventory.views OrderedMemoryEnsemble.providerView
  OrderedMemoryEnsemble.terminalView OrderedMemoryProvider.circuit OrderedBoundaryEnd.circuit
  SnapshotRegisterProvider.circuit SnapshotRamProvider.circuit
  FinalRegisterProvider.circuit FinalRamProvider.circuit
  ByteChip.U8Range.circuit ByteChip.MSB.circuit ByteChip.AndByte.circuit
  ByteChip.OrByte.circuit ByteChip.XorByte.circuit ByteChip.Ltu.circuit
  RangeChip.circuitFor RangeChip.circuit DecodedProgramProvider.circuit

private theorem source_lookupNames (source : ExecutionSnapshot) (component : Component (ZMod p))
    (member : component ∈ (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).views.map (·.component)) :
    component.operations.lookups.map (·.table.name) ⊆
      ["sp1.native.source_registers", "sp1.native.initial_memory"] := by
  simp only [SnapshotMemoryEnsemble.views_eq, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Component.lookups_eq, Component.rowOperations, circuit_norm,
      MemorySnapshot.registerTable, StaticTable.ofRows]

private theorem final_lookups (component : Component (ZMod p))
    (member : component ∈ FinalMemoryEnsemble.inventory.views.map (·.component)) :
    component.operations.lookups = [] := by
  change component ∈ [(FinalMemoryEnsemble.registerView (p := p)).component,
    (FinalMemoryEnsemble.ramView (p := p)).component,
    (OrderedMemoryEnsemble.terminalView OrderedFinalProvider.channelName (by decide)).component] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Component.lookups_eq, Component.rowOperations, circuit_norm]

private theorem provider_lookupNames (component : Component (ZMod p))
    (member : component ∈ sp1ProviderTables.take 23 ++ sp1ProviderTables.drop 26) :
    component.operations.lookups.map (·.table.name) ⊆ ["ByteXor"] := by
  change component ∈
    [{ circuit := ByteChip.U8Range.circuit }, { circuit := ByteChip.MSB.circuit },
     { circuit := ByteChip.AndByte.circuit }, { circuit := ByteChip.OrByte.circuit },
     { circuit := ByteChip.XorByte.circuit }, { circuit := ByteChip.Ltu.circuit }] ++
    sp1RangeProviderTables ++
    [{ circuit := MemoryBumpChip.circuit }, { circuit := StateBumpChip.circuit },
     { circuit := HaltChip.circuit }, { circuit := SyscallInstrsChip.circuit }] at member
  rcases List.mem_append.mp member with byteRange | system
  · rcases List.mem_append.mp byteRange with byte | range
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at byte
      rcases byte with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Component.lookups_eq, Component.rowOperations, circuit_norm, Gadgets.Xor.ByteXorTable]
    · obtain ⟨width, _, rfl⟩ := List.mem_map.mp range
      simp [Component.lookups_eq, Component.rowOperations, circuit_norm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at system
    rcases system with rfl | rfl | rfl | rfl
    all_goals simp only [MemoryBumpChip.lookups_empty, StateBumpChip.lookups_empty,
      HaltChip.lookups_empty, SyscallInstrsChip.lookups_empty, List.map_nil, List.nil_subset]

/-- Every local-core lookup reads one of the four authenticated static dependencies. -/
theorem lookup_names_subset (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ tables image source) :
    component.operations.lookups.map (·.table.name) ⊆
      ["sp1.native.source_registers", "sp1.native.initial_memory", "sp1.native.program", "ByteXor"] := by
  rcases List.mem_append.mp member with snapshot | rest
  · exact List.Subset.trans (source_lookupNames source component snapshot) (by simp)
  rcases List.mem_append.mp rest with retained | provider
  · rcases List.mem_append.mp retained with boundary | instruction
    · rcases List.mem_append.mp boundary with final | rom
      · simp [final_lookups component final]
      · obtain rfl := List.mem_singleton.mp rom
        simp [Component.lookups_eq, Component.rowOperations, circuit_norm,
          ProgramImage.programTable, StaticTable.ofRows]
    · simp [sp1Tables_lookups_empty component instruction]
  · exact List.Subset.trans (provider_lookupNames component provider) (by simp)

end SP1Clean.Soundness.LocalCore
