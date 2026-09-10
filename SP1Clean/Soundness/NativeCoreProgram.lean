import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.TypedProgram

/-! # Committed instruction fetches in the authenticated native core

The fixed image table authenticates every active Program fetch. All other native components are
silent or emit gated unit pulls. Clean's actual count-bounded balance therefore authenticates each
active fetch, independently of table order and of State/Memory grounding.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A structural Program consumer contributes only disabled interactions or unit pulls. -/
def ProgramPulls (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith programChannel.toRaw
      (Environment.fromArray physical data), interaction.mult = 0 ∨ interaction.mult = -1

omit [Fact (2 ^ 24 < p)] in
private theorem programPulls_of_silent (component : Component (ZMod p))
    (silent : programChannel.toRaw ∉ component.circuit.channels) : ProgramPulls component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

private theorem instruction_programPulls (component : Component (ZMod p))
    (member : component ∈ sp1Tables (p := p)) : ProgramPulls component := by
  obtain ⟨chip, chipMem, rfl⟩ := List.mem_map.mp member
  intro data physical constraints interaction emitted
  rw [supportedChip_programEmissionShape chip chipMem data physical constraints] at emitted
  obtain rfl := List.mem_singleton.mp emitted
  rcases supportedChip_selectorConstraintShape chip chipMem data physical constraints with zero | one
  · left
    change -(chip.decodeRow data physical).is_real = 0
    rw [show (chip.decodeRow data physical).is_real = 0 from zero, neg_zero]
  · right
    change -(chip.decodeRow data physical).is_real = -1
    rw [show (chip.decodeRow data physical).is_real = 1 from one]

omit [Fact (2 ^ 24 < p)] in
private theorem programPulls_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (message : Var Input (ZMod p) → Var ProgramMsg (ZMod p))
    (emission : ∀ input offset, ((circuit.main input).operations offset).interactionsWith
      programChannel.toRaw = [(programChannel.pulledIf (gate input) (message input)).toRaw])
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : ProgramPulls ⟨circuit⟩ := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((circuit.main (varFromOffset Input 0)).operations
    (size Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, neg_eq_zero, neg_inj]
  simpa only [CircuitType.eval_expr] using bound

private theorem halt_programPulls : ProgramPulls (⟨HaltChip.circuit⟩ : Component (ZMod p)) :=
  programPulls_of_gated HaltChip.circuit (fun input => input.is_real) HaltChip.programMsg
    HaltChip.interactionsWith_program_eq HaltChip.selectorBinary_of_shallow

private theorem syscall_programPulls : ProgramPulls (⟨SyscallInstrsChip.circuit⟩ : Component (ZMod p)) :=
  programPulls_of_gated SyscallInstrsChip.circuit (fun input => input.is_real) SyscallInstrsChip.programMsg
    Faithful.syscallInstrsInteractionsWith_program SyscallInstrsChip.selectorBinary_of_shallow

private theorem boundary_programPulls (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (InitialMemoryEnsemble.views image).map (·.component) ++
      FinalMemoryEnsemble.inventory.views.map (·.component)) : ProgramPulls component := by
  apply programPulls_of_silent
  simp only [InitialMemoryEnsemble.views, OrderedMemoryEnsemble.Inventory.views,
    FinalMemoryEnsemble.inventory, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      (List.replicate 42 byteChannel.toRaw ++
        [(OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw] ++
        List.replicate 4 byteChannel.toRaw ++
        [memoryChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw])
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, programChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
        memoryChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel,
      memoryChannel, byteChannel, Channel.toRaw]
  · change programChannel.toRaw ∉
      [byteChannel.toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw,
        (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedFinalProvider.channelName, programChannel, byteChannel, Channel.toRaw]

private theorem remainingProvider_programPulls (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23 ++ sp1ProviderTables.drop 26) :
    ProgramPulls component := by
  rw [sp1ProviderTables, ← List.map_take, ← List.map_drop, ← List.map_append] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have noProgram : .program ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noInit : .memoryInit ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  have noFinal : .memoryFinalize ∉ ProviderTableId.all.take 23 ++ ProviderTableId.all.drop 26 := by decide
  cases id with
  | program => exact (noProgram idMem).elim
  | memoryInit => exact (noInit idMem).elim
  | memoryFinalize => exact (noFinal idMem).elim
  | halt => exact halt_programPulls
  | syscallInstrs => exact syscall_programPulls
  | byte provider =>
      apply programPulls_of_silent
      cases provider <;> change programChannel.toRaw ∉ [byteChannel.toRaw]
      all_goals simp [programChannel_eq_byteChannel_false]
  | range width =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw]
      simp [programChannel_eq_byteChannel_false]
  | memoryBump =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw, memoryChannel.toRaw, memoryChannel.toRaw]
      simp [programChannel_eq_byteChannel_false, programChannel_eq_memoryChannel_false]
  | stateBump =>
      apply programPulls_of_silent
      change programChannel.toRaw ∉ [byteChannel.toRaw, stateChannel.toRaw]
      simp [programChannel_eq_byteChannel_false, programChannel_eq_stateChannel_false]

/-- The computed ROM is the only possible non-pull Program contributor in this assembly. -/
theorem component_program_source (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ (ensemble image).allTables) :
    component = (⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)) ∨ ProgramPulls component := by
  simp only [Ensemble.allTables, List.mem_cons] at member
  rcases member with rfl | member
  · right
    apply programPulls_of_silent
    change programChannel.toRaw ∉ [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw,
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]
    simp [OrderedBoundary.channel, OrderedInitialProvider.channelName, OrderedFinalProvider.channelName,
      stateChannel, programChannel, byteChannel, exitChannel, Channel.toRaw]
  · change component ∈ tables image at member
    simp only [tables, afterInitialTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with member | ((member | rfl) | member) | member
    · exact Or.inr (boundary_programPulls image component (List.mem_append_left _ member))
    · exact Or.inr (boundary_programPulls image component (List.mem_append_right _ member))
    · exact Or.inl rfl
    · exact Or.inr (instruction_programPulls component member)
    · exact Or.inr (remainingProvider_programPulls component (List.mem_append.mpr member))

/-- Every active Program pull in the combined AIR names a decoded instruction in the checked
image. No Program-truth premise, execution ordering, or semantic memory binding is required. -/
theorem program_pull_committed {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.mult = -1)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) := by
  have balance := balanced programChannel.toRaw (by simp [ensemble, sp1Ensemble_channels])
  obtain ⟨source, sourceMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balance interaction member active
  obtain ⟨table, tableMem, sourceMem⟩ := EnsembleWitness.mem_interactionsWith.mp sourceMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp sourceMem
  have checked := constraints table tableMem physical physicalMem
  rcases component_program_source image table.component
    (witness.mem_allTables_component_of_mem_allTables tableMem) with fixed | pulls
  · rw [fixed] at emitted checked
    have committed := DecodedProgramProvider.constraints_committed valid (table.environment physical) checked
    have same := (DecodedProgramProvider.program_interaction_payload image _ source emitted).symm.trans
      (samePayload.trans payload)
    have messageEq : ((⟨DecodedProgramProvider.circuit image⟩ : Component (ZMod p)).rowInput
        (table.environment physical)).toMessage = message := by
      have vectorEq := Vector.toArray_inj.mp same
      have decoded := congrArg (fromElements (M := ProgramMsg)) vectorEq
      simpa only [ProvableType.fromElements_toElements] using decoded
    rw [messageEq] at committed
    exact committed
  · exact ((pulls table.data physical checked source emitted).elim nonzero notPull).elim

end SP1Clean.Soundness.NativeCore
