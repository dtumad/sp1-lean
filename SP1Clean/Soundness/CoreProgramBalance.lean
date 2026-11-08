import SP1Clean.Soundness.NativeCoreFinalBoundary
import SP1Clean.Soundness.TypedProgram

/-! # Shared Program authentication for native core assemblies

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
      (Environment.fromArray physical data), interaction.mult = 0 ∨ interaction.Pull

omit [Fact (2 ^ 24 < p)] in
theorem programPulls_of_silent (component : Component (ZMod p))
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
    change (chip.decodeRow data physical).is_real = 0
    exact zero
  · right
    exact ⟨rfl, one⟩

omit [Fact (2 ^ 24 < p)] in
private theorem programPulls_of_gated {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (generation : WitnessGeneration.Generation (ZMod p) Input)
    (gate : Var Input (ZMod p) → Expression (ZMod p))
    (message : Var Input (ZMod p) → Var ProgramMsg (ZMod p))
    (emission : ∀ input offset, ((circuit.main input).operations offset).interactionsWith
      programChannel.toRaw = [(programChannel.pulledIf (gate input) (message input)).toRaw])
    (binary : ∀ input offset env,
      ConstraintsHold.Shallow env ((circuit.main input).operations offset) →
        env (gate input) = 0 ∨ env (gate input) = 1) : ProgramPulls { circuit, generation, Assumptions := circuit.Assumptions } := by
  intro data physical constraints interaction member
  have bound := binary (varFromOffset Input 0) (size Input) (Environment.fromArray physical data)
    (shallowConstraints_of_componentConstraints circuit _ constraints)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((circuit.main (varFromOffset Input 0)).operations
    (size Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [Channel.eval_pulledIf, Channel.pulledIfValue, Interaction.Pull, true_and]
  simpa only [CircuitType.eval_expr] using bound

private theorem halt_programPulls : ProgramPulls ({ circuit := HaltChip.circuit, Assumptions := (HaltChip.circuit).Assumptions, generation := HaltChip.generation } : Component (ZMod p)) :=
  programPulls_of_gated HaltChip.circuit HaltChip.generation (fun input => input.is_real) HaltChip.programMsg
    HaltChip.interactionsWith_program_eq HaltChip.selectorBinary_of_shallow

private theorem syscall_programPulls : ProgramPulls ({ circuit := SyscallInstrsChip.circuit, Assumptions := (SyscallInstrsChip.circuit).Assumptions, generation := SyscallInstrsChip.generation } : Component (ZMod p)) :=
  programPulls_of_gated SyscallInstrsChip.circuit SyscallInstrsChip.generation (fun input => input.is_real) SyscallInstrsChip.programMsg
    SyscallInstrsChip.Ledger.syscallInstrsInteractionsWith_program SyscallInstrsChip.selectorBinary_of_shallow

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

/-- Only the computed ROM can produce Program messages in the shared execution suffix. -/
theorem interior_program_source (image : ProgramImage) (component : Component (ZMod p))
    (member : component ∈ afterFinalTables image) :
    component = (FixedProgramProvider.Preprocessed.component image) ∨ ProgramPulls component := by
  simp only [afterFinalTables, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | instruction) | providers
  · exact Or.inl rfl
  · exact Or.inr (instruction_programPulls component instruction)
  · exact Or.inr (remainingProvider_programPulls component (List.mem_append.mpr providers))

/-- Count-bounded Program balance authenticates a pull whenever the checked ROM is the sole
possible producer. The enclosing ensemble and its source-state policy are arbitrary. -/
theorem program_pull_committed_of_sources {Public : TypeMap} [ProvableType Public]
    {assembly : Ensemble (ZMod p) Public} {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness assembly) (constraints : witness.Constraints)
    (balance : BalancedInteractions (witness.interactionsWith programChannel.toRaw))
    (verifier : ∀ (data : ProverData (ZMod p)),
      ∀ interaction ∈ assembly.verifierOperations.interactionValuesWith programChannel.toRaw
        data.publicEnvironment, interaction.mult = 0 ∨ interaction.Pull)
    (sources : ∀ component ∈ assembly.tables,
      component = (FixedProgramProvider.Preprocessed.component image) ∨ ProgramPulls component)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.Pull)
    (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) := by
  obtain ⟨source, sourceMem, samePayload, nonzero, notPull⟩ :=
    balance.exists_push_of_pull interaction member active
  rcases EnsembleWitness.mem_interactionsWith.mp sourceMem with verifierMem | ⟨table, tableMem, sourceMem⟩
  · exact ((verifier witness.data source verifierMem).elim nonzero (fun pull => notPull pull.1 pull.2)).elim
  · obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp sourceMem
    have checked := constraints table tableMem physical physicalMem
    have shared : table.data = witness.data := witness.same_data table tableMem
    simp only [Table.environment, shared] at checked emitted
    rcases sources table.component
      (EnsembleWitness.component_mem_tables_of_mem tableMem) with fixed | pulls
    · rw [fixed] at emitted checked
      have occurrence := FixedProgramProvider.Preprocessed.program_interaction image _ source emitted
      have counted : (valueFromOffset FixedProgramProvider.Preprocessed.Input 0
          (Environment.fromArray physical witness.data)).2 ≠ 0 := by
        rwa [← occurrence.2]
      have committed := FixedProgramProvider.Preprocessed.table_committed valid table fixed
        (constraints table tableMem)
        physical physicalMem (by simpa only [Table.environment, shared] using counted)
      simp only [Table.environment, shared] at committed
      have same := occurrence.1.symm.trans (samePayload.trans payload)
      have messageEq : (valueFromOffset FixedProgramProvider.Preprocessed.Input 0
          (Environment.fromArray physical witness.data)).1 = message := by
        have vectorEq := Vector.toArray_inj.mp same
        have decoded := congrArg (fromElements (M := ProgramMsg)) vectorEq
        simpa only [ProvableType.fromElements_toElements] using decoded
      rw [messageEq] at committed
      exact committed
    · exact ((pulls witness.data physical checked source emitted).elim nonzero (fun pull => notPull pull.1 pull.2)).elim

end SP1Clean.Soundness.NativeCore
