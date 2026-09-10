import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.MemoryFrontier
import SP1Clean.Soundness.GenericWalk

/-! # Actual Memory balance of the authenticated native core

The initial and final inventories delimit the complete physical Memory ledger. The interior
retains ordinary instructions, refreshes, HALT, and syscalls, including active syscall rows.
Constraints force unit signed multiplicities; count-bounded Clean balance then gives an exact
per-location equation with unique authenticated boundary records. No Memory guarantee or
execution-order premise is used to establish this equation.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics
open TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every physical Memory interaction is disabled or has unit signed multiplicity. -/
def MemoryBinary (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith memoryChannel.toRaw
      (Environment.fromArray physical data),
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1

omit [Fact (2 ^ 24 < p)] in
private theorem memoryBinary_of_silent (component : Component (ZMod p))
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
  exact signedVal_binary_of_selector_gated _ _
    (supportedChip_selectorConstraintShape chip chipMem data physical constraints)
    (supportedChip_memorySelectorConstraintShape chip chipMem data physical constraints source sourceMem)

private theorem memoryBinary_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (gated : ∀ input offset (env : Environment (ZMod p)),
      ∀ interaction ∈ ((circuit.main input).operations offset).interactionsWith memoryChannel.toRaw,
        env interaction.mult = -(env (gate input)) ∨ env interaction.mult = 0 ∨
          env interaction.mult = env (gate input))
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : MemoryBinary ⟨circuit⟩ := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp member
  exact signedVal_binary_of_selector_gated _ _ bound
    (gated (varFromOffset Input 0) (size Input) _ source sourceMem)

private theorem halt_memoryBinary : MemoryBinary (⟨HaltChip.circuit⟩ : Component (ZMod p)) := by
  apply memoryBinary_of_gated HaltChip.circuit (fun input => input.is_real) ?_
    HaltChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((HaltChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [HaltChip.interactionsWith_memory_eq]
  simp [HaltChip.exposedMemoryInteractions, Channel.pulledIf, Channel.pushedIf,
    ChannelInteraction.toRaw, pulledIf_mult, pushedIf_mult, Expression.eval]

private theorem syscall_memoryBinary : MemoryBinary (⟨SyscallInstrsChip.circuit⟩ : Component (ZMod p)) := by
  apply memoryBinary_of_gated SyscallInstrsChip.circuit (fun input => input.is_real) ?_
    SyscallInstrsChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((SyscallInstrsChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [Faithful.syscallInstrsInteractionsWith_memory]
  simp [ChannelInteraction.toRaw, Expression.eval]

private theorem memoryBump_memoryBinary : MemoryBinary (⟨MemoryBumpChip.circuit⟩ : Component (ZMod p)) := by
  apply memoryBinary_of_gated MemoryBumpChip.circuit (fun input => input.is_real) ?_
    MemoryBumpChip.selectorBinary_of_shallow
  intro input offset env
  change ∀ interaction ∈ ((MemoryBumpChip.main input).operations offset).interactionsWith memoryChannel.toRaw,
    env interaction.mult = -(env input.is_real) ∨ env interaction.mult = 0 ∨
      env interaction.mult = env input.is_real
  rw [memoryBumpMain_memoryInteractions]
  simp [Channel.pulledIf, Channel.pushedIf, ChannelInteraction.toRaw, pulledIf_mult,
    pushedIf_mult, Expression.eval]

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
    change memoryChannel.toRaw ∉ [programChannel.toRaw]
    simp [memoryChannel_eq_programChannel_false]
  · exact instruction_memoryBinary component member
  · exact remainingProvider_memoryBinary component (List.mem_append.mpr member)

/-- The unchanged physical Memory ledger after the two three-table inventories. -/
noncomputable def memoryInterior {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) : List (TypedInteraction (memoryChannel (p := p))) :=
  (witness.tables.drop 6).flatMap (typedTableInteractionsWith · memoryChannel)

/-- The interior adapter preserves every raw interaction, including disabled interactions. -/
theorem memoryInterior_raw {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    (memoryInterior witness).map TypedInteraction.raw =
      (witness.tables.drop 6).flatMap (·.interactionsWith memoryChannel.toRaw) := by
  simp only [memoryInterior, List.map_flatMap, typedTableInteractionsWith_raw]

private theorem verifier_memory_silent (image : ProgramImage) :
    memoryChannel.toRaw ∉ (verifier (p := p) image).channels := by
  change memoryChannel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
    (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
    (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
  simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
    stateChannel, memoryChannel, byteChannel, exitChannel, Channel.toRaw]

/-- Exact decomposition of the physical ledger into initial records, final records, and all
remaining interactions. The typed `pushedIfValue (-1)` is the finalizer's negative emission with
`assumeGuarantees = false`; signed message selection places it on the consumed side. -/
theorem memory_interactions {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) :
    typedEnsembleInteractionsWith witness memoryChannel =
      (InitialMemoryEnsemble.records (initialWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel 1) ++
      (FinalMemoryEnsemble.records (finalWitness witness)).map
        (TypedInteraction.pushedIfValue memoryChannel (-1)) ++
      memoryInterior witness := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedEnsembleInteractionsWith_raw, List.map_append, List.map_append, memoryInterior_raw]
  simp only [List.map_map]
  change witness.interactionsWith memoryChannel.toRaw =
    (InitialMemoryEnsemble.records (initialWitness witness)).map memoryChannel.pushedValue ++
    (FinalMemoryEnsemble.records (finalWitness witness)).map (memoryChannel.emittedValue (-1)) ++ _
  rw [← initial_memory_interactions witness, ← final_memory_interactions witness]
  change witness.verifierTable.interactionsWith memoryChannel.toRaw ++
    witness.tables.flatMap (·.interactionsWith memoryChannel.toRaw) = _
  rw [witness.verifierTable.interactionsWith_nil_of_channel_not_mem (verifier_memory_silent image),
    List.nil_append]
  have split := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith memoryChannel.toRaw))
    (List.take_append_drop 3 witness.tables)
  have splitTail := congrArg (List.flatMap (fun t : Table (ZMod p) => t.interactionsWith memoryChannel.toRaw))
    (List.take_append_drop 3 (witness.tables.drop 3))
  simp only [List.flatMap_append, List.drop_drop] at split splitTail
  rw [← split, ← splitTail, List.append_assoc]

/-- Every interaction of the unchanged interior has signed-unit multiplicity or zero. -/
theorem memoryInterior_signedBinary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints) :
    ∀ interaction ∈ memoryInterior witness,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  intro interaction member
  have rawMem := List.mem_map_of_mem (f := TypedInteraction.raw) member
  rw [memoryInterior_raw] at rawMem
  obtain ⟨table, tableMem, rowMem⟩ := List.mem_flatMap.mp rawMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp rowMem
  have componentMem := List.mem_map_of_mem (f := fun t : Table (ZMod p) => t.component) tableMem
  rw [List.map_drop, witness.tables_map_component] at componentMem
  change table.component ∈ afterFinalTables image at componentMem
  exact interior_memoryBinary image table.component componentMem table.data physical
    (constraints table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop tableMem))
      physical physicalMem) interaction.raw emitted

private theorem memory_unitSigns :
    signedVal (1 : ZMod p) = 1 ∧ signedVal (-1 : ZMod p) = -1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  constructor
  · rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num
  · rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    norm_num

private theorem initial_activeMessages (records : List (MemoryMsg (ZMod p))) :
    producedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel 1)) = records ∧
    consumedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel 1)) = [] := by
  simp [producedMessages, consumedMessages, List.filter_map, Function.comp_def, memory_unitSigns.1]

private theorem final_activeMessages (records : List (MemoryMsg (ZMod p))) :
    producedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel (-1))) = [] ∧
    consumedMessages (records.map (TypedInteraction.pushedIfValue memoryChannel (-1))) = records := by
  simp [producedMessages, consumedMessages, List.filter_map, Function.comp_def, memory_unitSigns.2]

/-- Raw constraints force signed-unit multiplicities throughout the combined Memory ledger.
This includes both inventories and all active system rows. -/
theorem memory_signedBinary {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (constraints : witness.Constraints) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨ signedVal interaction.mult = 1 := by
  rw [memory_interactions]
  intro interaction member
  rcases List.mem_append.mp member with boundary | interior
  · rcases List.mem_append.mp boundary with initial | final
    · obtain ⟨message, _, rfl⟩ := List.mem_map.mp initial
      exact Or.inr (Or.inr memory_unitSigns.1)
    · obtain ⟨message, _, rfl⟩ := List.mem_map.mp final
      exact Or.inl memory_unitSigns.2
  · exact memoryInterior_signedBinary witness constraints interaction interior

/-- Initial records and all interior pushes are a permutation of final records and all interior
pulls, as complete typed messages. Values, locations, and timestamps are preserved together. -/
theorem memory_records_perm {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    (InitialMemoryEnsemble.records (initialWitness witness) ++ producedMessages (memoryInterior witness)).Perm
      (FinalMemoryEnsemble.records (finalWitness witness) ++ consumedMessages (memoryInterior witness)) := by
  classical
  have balance : BalancedInteractions
      ((typedEnsembleInteractionsWith witness memoryChannel).map TypedInteraction.raw) := by
    rw [typedEnsembleInteractionsWith_raw]
    exact balanced _ (by simp [ensemble, sp1Ensemble_channels])
  have paired := producedMessages_perm_consumedMessages _ balance
    (memory_signedBinary witness constraints)
  simpa only [memory_interactions, producedMessages_append, consumedMessages_append,
    (initial_activeMessages _).1, (initial_activeMessages _).2,
    (final_activeMessages _).1, (final_activeMessages _).2, List.append_nil, List.nil_append] using paired

/-- The unique authenticated initial record at each touched location, if present. -/
noncomputable def memoryInitialFrontier {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((InitialMemoryEnsemble.records (initialWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- The unique final record at each finalized location, without assuming its value is current. -/
noncomputable def memoryFinalFrontier {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image)) (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((FinalMemoryEnsemble.records (finalWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem optMS_records_frontier (records : List (MemoryMsg (ZMod p)))
    (unique : (records.map MemoryMsg.locOf).Nodup) (loc : MemLoc) :
    optMS (records.filter (fun message => decide (MemoryMsg.locOf message = loc))).head? =
      Multiset.filter (fun message => MemoryMsg.locOf message = loc) (↑records : Multiset _) := by
  rw [optMS_head?_eq_coe _ (pairwise_distinct_filter_length_le_one MemoryMsg.locOf _ loc
    (List.pairwise_map.mp unique)), Multiset.filter_coe]

/-- The exact per-location Memory equation needed for timed grounding. Its endpoints are unique
records derived from this assembly's own ordering constraints and balance. No boundary uniqueness,
Memory truth, padding inactivity, or syscall inactivity is assumed. -/
theorem memory_frontier_balance {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (loc : MemLoc) :
    optMS (memoryInitialFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(producedMessages (memoryInterior witness)) : Multiset _) =
      optMS (memoryFinalFrontier witness loc) +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(consumedMessages (memoryInterior witness)) : Multiset _) := by
  rw [memoryInitialFrontier, memoryFinalFrontier,
    optMS_records_frontier _ (initial_records_locations_nodup witness constraints balanced),
    optMS_records_frontier _ (final_records_locations_nodup witness constraints balanced)]
  have same : (↑(InitialMemoryEnsemble.records (initialWitness witness) ++
      producedMessages (memoryInterior witness)) : Multiset (MemoryMsg (ZMod p))) =
      ↑(FinalMemoryEnsemble.records (finalWitness witness) ++ consumedMessages (memoryInterior witness)) :=
    Multiset.coe_eq_coe.mpr (memory_records_perm witness constraints balanced)
  have filtered := congrArg (Multiset.filter (fun message => MemoryMsg.locOf message = loc)) same
  simpa only [filter_coe_append] using filtered

/-- A present initial frontier record is authentic at the requested location. -/
theorem memoryInitialFrontier_authentic {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.InitialSpec image message := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  exact ⟨of_decide_eq_true member.2, initial_records_authentic witness constraints balanced _ member.1⟩

/-- A present final frontier record has the requested canonical location. Currency of its value
and validity of its clock are conclusions still to be supplied by the timed walk. -/
theorem memoryFinalFrontier_canonical {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryFinalFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.CanonicalSpec message := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  exact ⟨of_decide_eq_true member.2, final_records_canonical witness constraints balanced _ member.1⟩

/-- The authenticated initial inventory supplies the generic timed engine's complete live-memory
invariant at genesis. The trajectory need only start at the configured image state; no future
execution, Memory truth, or caller-supplied semantic boundary binding is assumed. -/
theorem memoryInitialFrontier_liveOK {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some image.initialSailState) :
    LiveOKG trajectory image.initialSailState timeline (timeline.start 0)
      (memoryInitialFrontier witness) := by
  intro loc message present
  obtain ⟨sameLoc, authentic⟩ := memoryInitialFrontier_authentic witness constraints balanced present
  have content := authentic.2.2.2.2.1
  have atStart : LocalValueAtG trajectory image.initialSailState timeline
      (MemoryMsg.locOf message) (timeline.start 0) message.value :=
    (localValueAtG_stepStart_iff initial).mpr content
  refine ⟨sameLoc, ⟨authentic.1, authentic.2.1, ?_⟩, ?_, ?_⟩
  · rw [authentic.2.2.1]
    by_cases zero : timeline.start 0 = 0
    · simpa only [zero] using atStart
    · simpa only [LocalValueAtG, microValueG, if_pos (Nat.pos_of_ne_zero zero)] using content
  · simpa only [sameLoc] using atStart
  · rw [authentic.2.2.1]
    exact Nat.zero_le _

end SP1Clean.Soundness.NativeCore
