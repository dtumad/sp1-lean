import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.MemoryFrontier

/-! # Shared Memory balance rules for the native core

Component-local multiplicity proofs cover the common instruction/provider suffix used by both
boot and local assemblies. Boolean boundary activities reduce count-bounded Clean balance to an exact
record permutation and per-location optional-frontier equation. No execution or value-currency
premise enters these algebraic rules.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every physical Memory interaction is disabled or has unit multiplicity. -/
def MemoryBinary (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith memoryChannel.toRaw
      (Environment.fromArray physical data),
      IsBool interaction.mult

omit [Fact (2 ^ 24 < p)] in
/-- Components with no Memory interactions satisfy the multiplicity condition without constraints. -/
theorem memoryBinary_of_silent (component : Component (ZMod p))
    (silent : memoryChannel.toRaw ∉ component.circuit.channels) : MemoryBinary component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith memoryChannel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

private theorem instruction_memoryBinary (component : Component (ZMod p))
    (member : component ∈ sp1Tables (p := p)) : MemoryBinary component := by
  obtain ⟨chip, chipMem, rfl⟩ := List.mem_map.mp member
  intro data physical constraints interaction emitted
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp emitted
  rcases supportedChip_memorySelectorConstraintShape chip chipMem data physical constraints
    source sourceMem with zero | selector
  · exact Or.inl zero
  · change IsBool (Expression.eval (Environment.fromArray physical data) source.mult)
    rw [selector]
    exact supportedChip_selectorConstraintShape chip chipMem data physical constraints

omit [Fact (2 ^ 24 < p)] in
private theorem memoryBinary_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (generation : WitnessGeneration.Generation (ZMod p) Input)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (gated : ∀ input offset (env : Environment (ZMod p)),
      ∀ interaction ∈ ((circuit.main input).operations offset).interactionsWith memoryChannel.toRaw,
        env interaction.mult = 0 ∨
          env interaction.mult = env (gate input))
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : MemoryBinary { circuit, Assumptions := circuit.Assumptions, generation } := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp member
  rcases gated (varFromOffset Input 0) (size Input) _ source sourceMem with zero | selector
  · exact Or.inl zero
  · change IsBool ((Environment.fromArray physical data) source.mult)
    rw [selector]
    exact bound

private theorem halt_memoryBinary : MemoryBinary ({ circuit := HaltChip.circuit, Assumptions := (HaltChip.circuit).Assumptions, generation := HaltChip.generation } : Component (ZMod p)) := by
  apply memoryBinary_of_gated HaltChip.circuit HaltChip.generation (fun input => input.is_real) ?_
    HaltChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((HaltChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [HaltChip.interactionsWith_memory_eq]
  simp [HaltChip.exposedMemoryInteractions, Channel.pulledIf, Channel.pushedIf,
    ChannelInteraction.toRaw, pulledIf_mult, pushedIf_mult]

private theorem syscall_memoryBinary : MemoryBinary ({ circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation } : Component (ZMod p)) := by
  apply memoryBinary_of_gated SyscallInstrsChip.circuit SyscallInstrsChip.generation (fun input => input.is_real) ?_
    SyscallInstrsChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((SyscallInstrsChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [SyscallInstrsChip.Ledger.syscallInstrsInteractionsWith_memory]
  simp [ChannelInteraction.toRaw]

private theorem memoryBump_memoryBinary : MemoryBinary ({ circuit := MemoryBumpChip.circuit, Assumptions := (MemoryBumpChip.circuit).Assumptions, generation := MemoryBumpChip.generation } : Component (ZMod p)) := by
  apply memoryBinary_of_gated MemoryBumpChip.circuit MemoryBumpChip.generation (fun input => input.is_real) ?_
    MemoryBumpChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((MemoryBumpChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [memoryBumpMain_memoryInteractions]
  simp [Channel.pulledIf, Channel.pushedIf, ChannelInteraction.toRaw, pulledIf_mult,
    pushedIf_mult]

private theorem remainingProvider_memoryBinary (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23 ++ sp1ProviderTables.drop 26) :
    MemoryBinary component := by
  rw [sp1ProviderTables, ← List.map_take, ← List.map_drop, ← List.map_append] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have noProgram : .program ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noInit : .memoryInit ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noFinal : .memoryFinalize ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  cases id with
  | program => exact (noProgram idMem).elim
  | memoryInit => exact (noInit idMem).elim
  | memoryFinalize => exact (noFinal idMem).elim
  | halt => exact halt_memoryBinary
  | syscallInstrs => exact syscall_memoryBinary
  | memoryBump => exact memoryBump_memoryBinary
  | byte provider =>
      apply memoryBinary_of_silent
      cases provider <;> change memoryChannel.toRaw ∉ [byteChannel.toRaw]
      all_goals simp [memoryChannel_eq_byteChannel_false]
  | range width =>
      apply memoryBinary_of_silent
      change memoryChannel.toRaw ∉ [byteChannel.toRaw]
      simp [memoryChannel_eq_byteChannel_false]
  | stateBump =>
      apply memoryBinary_of_silent
      change memoryChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [memoryChannel_eq_byteChannel_false, memoryChannel_eq_stateChannel_false]

/-- Unit Memory multiplicities for every component after the two boundary inventories. -/
theorem interior_memoryBinary (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ afterFinalTables image) : MemoryBinary component := by
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · apply memoryBinary_of_silent
    change (memoryChannel (p := p)).toRaw ∉
      (FixedProgramProvider.Preprocessed.circuit (p := p) image).channels
    rw [FixedProgramProvider.Preprocessed.circuit_channels]
    simp [memoryChannel_eq_programChannel_false]
  · exact instruction_memoryBinary component member
  · exact remainingProvider_memoryBinary component (List.mem_append.mpr member)

omit [Fact (2 ^ 24 < p)] in
private theorem initial_activeMessages (records : List (ZMod p × MemoryMsg (ZMod p)))
    (binary : ∀ row ∈ records, row.1 = 0 ∨ row.1 = 1) :
    producedMessages (records.map (fun row => TypedInteraction.pushedIfValue memoryChannel row.1 row.2)) =
      (records.filter fun row => decide (row.1 = 1)).map Prod.snd ∧
    consumedMessages (records.map (fun row => TypedInteraction.pushedIfValue memoryChannel row.1 row.2)) = [] := by
  induction records with
  | nil => simp [producedMessages, consumedMessages]
  | cons row rows ih =>
    have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
    rcases binary row (List.mem_cons_self ..) with inactive | active
    · simpa [producedMessages, consumedMessages,
        inactive, TypedInteraction.mult, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
        Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.message, ProvableType.fromElements_toElements] using tail
    · simpa [producedMessages, consumedMessages,
        active, TypedInteraction.mult, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
        Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.message, ProvableType.fromElements_toElements] using tail

omit [Fact (2 ^ 24 < p)] in
private theorem final_activeMessages (records : List (ZMod p × MemoryMsg (ZMod p)))
    (binary : ∀ row ∈ records, row.1 = 0 ∨ row.1 = 1) :
    producedMessages (records.map (fun row => TypedInteraction.pulledIfValue memoryChannel row.1 row.2)) = [] ∧
    consumedMessages (records.map (fun row => TypedInteraction.pulledIfValue memoryChannel row.1 row.2)) =
      (records.filter fun row => decide (row.1 = 1)).map Prod.snd := by
  induction records with
  | nil => simp [producedMessages, consumedMessages]
  | cons row rows ih =>
    have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
    rcases binary row (List.mem_cons_self ..) with inactive | active
    · simpa [producedMessages, consumedMessages,
        inactive, TypedInteraction.mult, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
        Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.message, ProvableType.fromElements_toElements] using tail
    · simpa [producedMessages, consumedMessages,
        active, TypedInteraction.mult, TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
        Channel.pulledIfValue, Channel.pushedIfValue, TypedInteraction.message, ProvableType.fromElements_toElements] using tail

omit [Fact (2 ^ 24 < p)] in
/-- Boolean boundary activities preserve boolean counts of the complete physical ledger. -/
theorem memoryBoundary_binary (initial final : List (ZMod p × MemoryMsg (ZMod p)))
    (interior : List (TypedInteraction (memoryChannel (p := p))))
    (initialBinary : ∀ row ∈ initial, row.1 = 0 ∨ row.1 = 1)
    (finalBinary : ∀ row ∈ final, row.1 = 0 ∨ row.1 = 1)
    (binary : ∀ interaction ∈ interior,
      IsBool interaction.mult) :
    ∀ interaction ∈ initial.map (fun row => TypedInteraction.pushedIfValue memoryChannel row.1 row.2) ++
      final.map (fun row => TypedInteraction.pulledIfValue memoryChannel row.1 row.2) ++ interior,
      IsBool interaction.mult := by
  intro interaction member
  rcases List.mem_append.mp member with boundary | inside
  · rcases List.mem_append.mp boundary with initial | final
    · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp initial
      exact initialBinary row rowMem
    · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp final
      exact finalBinary row rowMem
  · exact binary interaction inside

omit [Fact (2 ^ 24 < p)] in
/-- Full physical balance gives an active-record permutation without discarding its count bound. -/
theorem memoryBoundary_records_perm (initial final : List (ZMod p × MemoryMsg (ZMod p)))
    (interior : List (TypedInteraction (memoryChannel (p := p))))
    (initialBinary : ∀ row ∈ initial, row.1 = 0 ∨ row.1 = 1)
    (finalBinary : ∀ row ∈ final, row.1 = 0 ∨ row.1 = 1)
    (binary : ∀ interaction ∈ interior,
      IsBool interaction.mult)
    (balanced : BalancedInteractions
      ((initial.map (fun row => TypedInteraction.pushedIfValue memoryChannel row.1 row.2) ++
        final.map (fun row => TypedInteraction.pulledIfValue memoryChannel row.1 row.2) ++ interior).map
          TypedInteraction.raw)) :
    (((initial.filter fun row => decide (row.1 = 1)).map Prod.snd) ++ producedMessages interior).Perm
      (((final.filter fun row => decide (row.1 = 1)).map Prod.snd) ++ consumedMessages interior) := by
  classical
  have paired := producedMessages_perm_consumedMessages _ balanced
    (memoryBoundary_binary initial final interior initialBinary finalBinary binary)
  simpa only [producedMessages_append, consumedMessages_append,
    (initial_activeMessages _ initialBinary).1, (initial_activeMessages _ initialBinary).2,
    (final_activeMessages _ finalBinary).1, (final_activeMessages _ finalBinary).2,
    List.append_nil, List.nil_append] using paired


omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem optMS_records_frontier (records : List (MemoryMsg (ZMod p)))
    (unique : (records.map MemoryMsg.locOf).Nodup) (loc : MemLoc) :
    optMS (records.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑records : Multiset _) := by
  rw [optMS_head?_eq_coe _ (pairwise_distinct_filter_length_le_one MemoryMsg.locOf _ loc
    (List.pairwise_map.mp unique)), Multiset.filter_coe]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Distinct boundary locations turn the record permutation into the timed engine's equation. -/
theorem memoryBoundary_frontier_balance (initial final produced consumed : List (MemoryMsg (ZMod p)))
    (initialUnique : (initial.map MemoryMsg.locOf).Nodup)
    (finalUnique : (final.map MemoryMsg.locOf).Nodup)
    (balanced : (initial ++ produced).Perm (final ++ consumed)) (loc : MemLoc) :
    optMS (initial.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑produced : Multiset _) =
      optMS (final.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑consumed : Multiset _) := by
  rw [optMS_records_frontier _ initialUnique, optMS_records_frontier _ finalUnique]
  have filtered := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc))
    (Multiset.coe_eq_coe.mpr balanced)
  simpa only [filter_coe_append] using filtered

end SP1Clean.Soundness.NativeCore
