import SP1Clean.Soundness.HostLocalCoreLedger
import SP1Clean.Soundness.LocalCoreMemory

/-! # Memory accounting with physical host accesses retained

The host extension keeps the two boundary inventories unchanged. Its interior is read from
the actual tables, including the wrapper's x12 accesses and every appended host RAM row.
No Memory balance is projected to the smaller instruction-only assembly.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance memoryLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance memoryLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

private theorem boundary_components (index : Fin 6) :
    (tables (p := p) image source auxiliary)[index.val]'(by rw [tables_length]; omega) =
      (LocalCore.tables image source)[index.val]'(by rw [LocalCore.tables_length]; omega) := by
  have bound := index.isLt
  rw [core_component image source auxiliary ⟨index.val, by omega⟩,
    if_neg (show ¬58 = index.val by omega)]
  simp only [ProtectedLocalCore.tables]
  rw [List.getElem_append_left (by simp only [List.length_set, LocalCore.tables_length]; omega)]
  simp only [List.getElem_set_ne (show 28 ≠ index.val by omega),
    List.getElem_set_ne (show 27 ≠ index.val by omega),
    List.getElem_set_ne (show 26 ≠ index.val by omega),
    List.getElem_set_ne (show 25 ≠ index.val by omega)]

/-- The original component view retains each physical table and its prover data. -/
theorem localWitness_table (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (index : Fin 59) :
    (localWitness witness).tables[index.val]'(by
      rw [← (localWitness witness).same_length]; change index.val < (LocalCore.tables image source).length
      rw [LocalCore.tables_length]; exact index.isLt) =
    (witness.tables[index.val]'(by
      rw [← witness.same_length]; change index.val < (tables image source auxiliary).length
      rw [tables_length]; omega)).withComponent
      ((LocalCore.tables image source)[index.val]'(by rw [LocalCore.tables_length]; exact index.isLt)) :=
  witness.project_getElem _ ⟨index.val, by
    change index.val < (LocalCore.tables image source).length
    rw [LocalCore.tables_length]; exact index.isLt⟩

/-- The typed wrapper ledger retains the original row plus the actual gated x12 pair. -/
theorem wrapper_memory_interactions (env : Environment (ZMod p))
    (constraints : HostCallLedger.producer.operations.ConstraintsHold env) :
    typedInteractionValuesWith HostCallLedger.producer.operations memoryChannel env =
      typedInteractionValuesWith HostCallProjection.original.operations memoryChannel env ++
      [TypedInteraction.pulledIfValue memoryChannel (HostCallProjection.extraRead env).is_real
        (HostCallProjection.extraRead env).prior,
       TypedInteraction.pushedIfValue memoryChannel (HostCallProjection.extraRead env).is_real
        (HostCallProjection.extraRead env).pushed] := by
  apply List.map_injective_iff.mpr TypedInteraction.raw_injective
  simp only [List.map_append, typedInteractionValuesWith_raw, List.map_cons, List.map_nil,
    TypedInteraction.pulledIfValue_raw, TypedInteraction.pushedIfValue_raw]
  exact HostCallProjection.memory_values env constraints

/-- Both boundary inventories retain their components, physical arrays, and prover data. -/
theorem boundary_tables (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (localWitness witness).tables.take 6 = witness.tables.take 6 := by
  apply witness.project_take (target := LocalCore.ensemble image source) _ 6
    (by change 6 ≤ (LocalCore.tables image source).length; rw [LocalCore.tables_length]; decide)
  intro index
  exact (boundary_components index).symm

/-- Every physical interior interaction, including zero multiplicities, is retained. -/
noncomputable def memoryInterior (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  (witness.tables.drop 6).flatMap (typedTableInteractionsWith · memoryChannel)

theorem memoryInterior_raw (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (memoryInterior witness).map TypedInteraction.raw =
      (witness.tables.drop 6).flatMap (·.interactionsWith memoryChannel.toRaw) := by
  simp only [memoryInterior, List.map_flatMap, typedTableInteractionsWith_raw]

/-- Exact full-ledger decomposition into the unchanged boundaries and the extended interior. -/
theorem memory_interactions (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    typedEnsembleInteractionsWith witness memoryChannel =
      ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
        (LocalCore.sourceWitness (localWitness witness))).map
          (TypedInteraction.pushedIfValue memoryChannel 1) ++
      (FinalMemoryEnsemble.records (LocalCore.finalWitness (localWitness witness))).map
        (TypedInteraction.pushedIfValue memoryChannel (-1)) ++ memoryInterior witness := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedEnsembleInteractionsWith_raw, List.map_append, List.map_append, memoryInterior_raw]
  simp only [List.map_map]
  change witness.interactionsWith memoryChannel.toRaw =
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
      (LocalCore.sourceWitness (localWitness witness))).map memoryChannel.pushedValue ++
    (FinalMemoryEnsemble.records (LocalCore.finalWitness (localWitness witness))).map
      (memoryChannel.emittedValue (-1)) ++ _
  rw [← LocalCore.source_memory_interactions, ← LocalCore.final_memory_interactions]
  change witness.interactionsWith memoryChannel.toRaw =
    ((localWitness witness).tables.take 3).flatMap (·.interactionsWith memoryChannel.toRaw) ++
    (((localWitness witness).tables.drop 3).take 3).flatMap (·.interactionsWith memoryChannel.toRaw) ++ _
  rw [← List.flatMap_append, ← List.take_add, boundary_tables]
  change witness.verifierTable.interactionsWith memoryChannel.toRaw ++
    witness.tables.flatMap (·.interactionsWith memoryChannel.toRaw) = _
  have silent : memoryChannel.toRaw ∉ (LocalCore.verifier (p := p) image source).channels := by
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at present
    contradiction
  rw [Table.interactionsWith_nil_of_channel_not_mem silent, List.nil_append,
    ← List.flatMap_append, List.take_append_drop]

private theorem wrapper_memorySigns (input : Var HostCallChip.Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (checked : ((HostCallChip.main input).operations offset).ConstraintsHold env) :
    ∀ interaction ∈ ((HostCallChip.main input).operations offset).interactionValuesWith memoryChannel.toRaw env,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  have real := (CoreSyscallChip.profile_of_constraints input.instruction offset env
    (HostCallChip.instruction_of_constraints input offset env checked)).1
  have evalReal (row : Var SyscallInstrsChip.Inputs (ZMod p)) :
      (eval env row).is_real = env row.is_real := by cases row; simp only [circuit_norm]
  rw [evalReal] at real
  have flag := HostCallChip.selector_of_constraints input offset env checked
  have readBinary : env (input.read (HostCallChip.selector input offset)).is_real = 0 ∨
      env (input.read (HostCallChip.selector input offset)).is_real = 1 := by
    change env (input.instruction.is_real * HostCallChip.selector input offset) = 0 ∨
      env (input.instruction.is_real * HostCallChip.selector input offset) = 1
    change env input.instruction.is_real * env (HostCallChip.selector input offset) = 0 ∨
      env input.instruction.is_real * env (HostCallChip.selector input offset) = 1
    simp only [flag, HostCallChip.writeFlag]
    split
    · simpa only [mul_one] using real
    · simp only [mul_zero, eq_self, true_or]
  intro interaction member
  rw [Operations.interactionValuesWith, HostCallChip.main_memory_interactions, List.map_append] at member
  rcases List.mem_append.mp member with original | extra
  · simp only [CoreSyscallChip.circuit, CoreSyscallChip.main, circuit_norm,
      GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
      SyscallCodeGuard.circuit, SyscallCodeGuard.main, SyscallInstrsChip.circuit,
      Operations.interactionsWith] at original
    change interaction ∈ (((SyscallInstrsChip.main input.instruction).operations offset).interactionsWith
      memoryChannel.toRaw).map _ at original
    rw [Faithful.syscallInstrsInteractionsWith_memory] at original
    apply signedVal_binary_of_selector_gated _ _ real
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at original
    rcases original with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [AbstractInteraction.eval, ChannelInteraction.toRaw, eval_neg, eq_self, true_or, or_true]
  · apply signedVal_binary_of_selector_gated _ _ readBinary
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at extra
    rcases extra with rfl | rfl
    all_goals simp only [AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.pulledIf,
      Channel.pushedIf, pulledIf, pushedIf, eval_neg, eq_self, true_or, or_true]

private theorem wrapper_memoryBinary : NativeCore.MemoryBinary (HostCallLedger.producer (p := p)) := by
  intro data physical constraints
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  exact wrapper_memorySigns (varFromOffset HostCallChip.Inputs 0) (size HostCallChip.Inputs)
    (Environment.fromArray physical data) ((Component.constraintsHold_iff _).mp constraints)

private theorem interior_component_binary
    (binary : ∀ component ∈ auxiliary, NativeCore.MemoryBinary component)
    (component : Component (ZMod p)) (member : component ∈ (tables image source auxiliary).drop 6) :
    NativeCore.MemoryBinary component := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  rw [List.getElem_drop]
  by_cases core : 6 + index < 59
  · rw [core_component image source auxiliary ⟨6 + index, core⟩]
    split
    · exact wrapper_memoryBinary
    · have projection := ProtectedLocalCore.component_projection (p := p) image source ⟨6 + index, core⟩
      have retained : ((LocalCore.tables (p := p) image source).drop 6)[index]'(by
          rw [List.length_drop, LocalCore.tables_length]; omega) ∈
          (LocalCore.tables (p := p) image source).drop 6 := List.getElem_mem _
      have old := NativeCore.interior_memoryBinary (p := p) image
        ((LocalCore.tables (p := p) image source)[6 + index]'(by rw [LocalCore.tables_length]; exact core))
        (by
          simp only [List.getElem_drop] at retained
          change (LocalCore.tables (p := p) image source)[6 + index] ∈ NativeCore.afterFinalTables image at retained
          exact retained)
      intro data physical constraints interaction emitted
      apply old data physical (by
        simpa only [Operations.ConstraintsHold, projection.1, projection.2.1] using constraints) interaction
      simpa only [Operations.interactionValuesWith, projection.2.2 memoryChannel.toRaw (by
        simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw])] using emitted
  · by_cases last : 6 + index = 59
    · have equal : index = 53 := by omega
      subst index
      change NativeCore.MemoryBinary (⟨WritePermissionProvider.circuit image⟩ : Component (ZMod p))
      apply NativeCore.memoryBinary_of_silent
      change memoryChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
      simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw]
    · have extra : 60 ≤ 6 + index := by omega
      simp only [tables] at bound ⊢
      rw [List.getElem_append_right (by
        simp only [List.length_set, ProtectedLocalCore.tables_length]; exact extra)]
      exact binary _ (List.getElem_mem _)

/-- Constraints force unit signed Memory multiplicities in the retained core, including WRITE's
x12 pair. Appended components supply only their static multiplicity property. -/
theorem memoryInterior_signedBinary (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints)
    (binary : ∀ component ∈ auxiliary, NativeCore.MemoryBinary component) :
    ∀ interaction ∈ memoryInterior witness,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  have rawMem := List.mem_map_of_mem (f := TypedInteraction.raw) member
  rw [memoryInterior_raw] at rawMem
  obtain ⟨table, tableMem, rowMem⟩ := List.mem_flatMap.mp rawMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp rowMem
  have componentMem := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) tableMem
  rw [List.map_drop, witness.tables_map_component] at componentMem
  exact interior_component_binary binary table.component componentMem table.data physical
    (constraints table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop tableMem))
      physical physicalMem) interaction.raw emitted

/-- Full Memory balance gives exact equality of the two record inventories, retaining every
host access. No projected Memory balance, semantic truth, or instruction inactivity is assumed. -/
theorem memory_records_perm (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (binary : ∀ component ∈ auxiliary, NativeCore.MemoryBinary component) :
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
      (LocalCore.sourceWitness (localWitness witness)) ++ producedMessages (memoryInterior witness)).Perm
    (FinalMemoryEnsemble.records (LocalCore.finalWitness (localWitness witness)) ++
      consumedMessages (memoryInterior witness)) := by
  apply NativeCore.memoryBoundary_records_perm _ _ _ (memoryInterior_signedBinary witness constraints binary)
  rw [← memory_interactions, typedEnsembleInteractionsWith_raw]
  exact balanced _ (by simp [ensemble, ProtectedLocalCore.ensemble, LocalCore.ensemble, sp1Ensemble_channels])

end SP1Clean.Soundness.HostLocalCore
