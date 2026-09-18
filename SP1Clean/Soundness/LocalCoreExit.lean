import SP1Clean.Soundness.LocalCoreRows
import SP1Clean.Soundness.ExitAccounting
import ToClean.Air.UnitBalance

/-! # Exit accounting from the local shard's complete physical ledger

Only the legacy HALT table and the syscall instruction table emit Exit messages. The verifier
consumes the public code once. Disabled interactions remain in the original count bound; the
generic unit-balance theorem then identifies every active emission with that code. A legacy
padding row still emits zero, so this value alone does not authenticate terminal status.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Channels Model.Core NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance exitLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}

private theorem verifierMain_exit (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((verifierMain image source input).operations offset).interactionsWith exitChannel.toRaw =
      [(exitChannel.pulled ⟨input.exit_code⟩).toRaw] := by
  have silent (name : String) (different : name ≠ "SP1Exit") (offset : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil
      (OrderedBoundaryVerifier.circuit (p := p) name
        OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).base
      exitChannel.toRaw () offset (by
        change exitChannel.toRaw ∉ [(OrderedBoundary.channel name).toRaw]
        simp [exitChannel, OrderedBoundary.channel, Channel.toRaw, Ne.symm different])
  have initial := silent SnapshotMemoryEnsemble.channelName (by decide)
  have final := silent OrderedFinalProvider.channelName (by decide)
  have preserved : ((verifierMain image source input).operations offset).interactionsWith exitChannel.toRaw =
      ((sp1StateVerifierMain input).operations offset).interactionsWith exitChannel.toRaw := by
    simp only [verifierMain, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions,
      Operations.interactionsWith, OrderedBoundaryVerifier.circuit] at initial final ⊢
    simp only [List.filter_append, initial, final, List.append_nil, sp1StateVerifier]
    rfl
  exact preserved.trans (sp1StateVerifierMain_exitInteractions input offset)

private theorem verifier_exit (witness : EnsembleWitness (ensemble (p := p) image source)) :
    witness.verifierTable.interactionsWith exitChannel.toRaw =
      [exitChannel.pulledValue ⟨witness.publicInput.exit_code⟩] := by
  have inputEval := ProvableType.eval_fromInput_varFromOffset_zero witness.publicInput witness.data
  have exitEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).exit_code⟩ : ExitMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) := by
    rw [eval_exitCodeMessage, inputEval]
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap,
    Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromInput witness.publicInput witness.data))
    (((verifierMain image source (varFromOffset SP1PublicIO 0)).operations
      (size SP1PublicIO)).interactionsWith exitChannel.toRaw) = _
  rw [verifierMain_exit]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, exitEval]

private theorem prefix_silent (witness : EnsembleWitness (ensemble (p := p) image source)) :
    (witness.tables.take 57).flatMap (·.interactionsWith exitChannel.toRaw) = [] := by
  have checked : ((tables (p := p) image source).take 57).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains
        (exitChannel (p := p)).toRaw.name) = true := rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply Table.interactionsWith_nil_of_channel_not_mem
  have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component] at mapped
  have absent := List.all_eq_true.mp checked table.component mapped
  intro used
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
  contradiction

/-- Every physical Exit producer, retaining both gates of each legacy HALT row. -/
noncomputable def exitProducers (witness : EnsembleWitness (ensemble (p := p) image source)) :
    List (ZMod p × ExitMsg (ZMod p)) :=
  (systemTable witness 2).table.flatMap (fun physical =>
    let row := haltRow (systemTable witness 2) physical
    [(row.is_real, HaltChip.exitMessage row), (1 - row.is_real, ⟨0⟩)]) ++
  (systemTable witness 3).table.map (fun physical =>
    let row := syscallInstrsRow (systemTable witness 3) physical
    (row.is_halt, SyscallInstrsChip.exitMessage row))

/-- No other table contributes to the local Exit ledger. -/
theorem exit_interactions (witness : EnsembleWitness (ensemble (p := p) image source)) :
    witness.interactionsWith exitChannel.toRaw =
      [exitChannel.pulledValue ⟨witness.publicInput.exit_code⟩] ++
        (exitProducers witness).map (fun entry => exitChannel.pushedIfValue entry.1 entry.2) := by
  have length : witness.tables.length = 59 := by
    rw [← witness.same_length]; exact tables_length image source
  have tail : witness.tables.drop 57 = [systemTable witness 2, systemTable witness 3] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_nil_of_le (by omega)]
    rfl
  have halt := congrArg (List.map TypedInteraction.raw)
    (haltTable_typedExit_of_component _ (systemTable_component witness 2))
  have syscall := congrArg (List.map TypedInteraction.raw)
    (syscallInstrsTable_typedExit_of_component _ (systemTable_component witness 3))
  simp only [typedTableInteractionsWith_raw, List.map_flatMap, List.map_cons,
    List.map_nil, TypedInteraction.pushedIfValue_raw] at halt syscall
  rw [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons, verifier_exit]
  have split := congrArg (List.flatMap (fun table : Table (ZMod p) => table.interactionsWith exitChannel.toRaw))
    (List.take_append_drop 57 witness.tables)
  rw [List.flatMap_append, prefix_silent, List.nil_append, tail] at split
  rw [← split]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, halt, syscall,
    exitProducers, List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, ← List.map_eq_flatMap]

private theorem legacy_binary {Row : Type*} (rows : List Row)
    (gate : Row → ZMod p) (message : Row → ExitMsg (ZMod p))
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ∀ entry ∈ rows.flatMap (fun row => [(gate row, message row), (1 - gate row, ⟨0⟩)]),
      entry.1 = 0 ∨ entry.1 = 1 := by
  intro entry member
  obtain ⟨row, rowMem, member⟩ := List.mem_flatMap.mp member
  have binary := binary row rowMem
  rcases List.mem_cons.mp member with rfl | member
  · exact binary
  · obtain rfl := List.mem_singleton.mp member
    rcases binary with equal | equal <;> simp [equal]

private theorem exitProducers_binary (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) :
    ∀ entry ∈ exitProducers witness, entry.1 = 0 ∨ entry.1 = 1 := by
  intro entry member
  simp only [exitProducers] at member
  rcases List.mem_append.mp member with legacy | syscall
  · exact legacy_binary _ _ _
      (haltRow_binary _ (systemTable_component witness 2) (systemTable_constraints witness constraints 2))
      entry legacy
  · have binary : ∀ physical ∈ (systemTable witness 3).table,
        (syscallInstrsRow (systemTable witness 3) physical).is_halt = 0 ∨
          (syscallInstrsRow (systemTable witness 3) physical).is_halt = 1 :=
      fun _ present => syscall_halt_binary _ (systemTable_component witness 3)
        (systemTable_constraints witness constraints 3) present
    have map_binary {Row : Type} (rows : List Row) (gate : Row → ZMod p)
        (message : Row → ExitMsg (ZMod p))
        (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
        ∀ entry ∈ rows.map (fun row => (gate row, message row)), entry.1 = 0 ∨ entry.1 = 1 := by
      intro entry member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact binary row present
    exact map_binary _ _ _ binary entry syscall

/-- Complete count-bounded balance leaves exactly one actual Exit emission. This includes
the legacy padding emission and makes no claim that zero means running. -/
theorem exit_messages (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel exitChannel.toRaw) :
    ((exitProducers witness).filter (fun entry => decide (entry.1 = 1))).map Prod.snd =
      [⟨witness.publicInput.exit_code⟩] := by
  apply List.perm_singleton.mp
  apply exitChannel.gated_unit_perm_of_balanced _ Prod.fst Prod.snd _
    (exitProducers_binary witness constraints)
  have ledger := balanced
  change BalancedInteractions (witness.interactionsWith exitChannel.toRaw) at ledger
  rw [exit_interactions] at ledger
  exact balancedInteractions_of_perm ledger (List.perm_append_comm ..)

private theorem exit_code_of_mem (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel exitChannel.toRaw)
    (message : ExitMsg (ZMod p)) (member : (1, message) ∈ exitProducers witness) :
    message.value = witness.publicInput.exit_code := by
  have active : message ∈ ((exitProducers witness).filter (fun entry => decide (entry.1 = 1))).map Prod.snd :=
    List.mem_map_of_mem (f := Prod.snd) (List.mem_filter.mpr ⟨member, by simp⟩)
  rw [exit_messages witness constraints balanced, List.mem_singleton] at active
  exact congrArg ExitMsg.value active

/-- An active legacy HALT binds its actual argument to the public Exit value. -/
theorem halt_exit_code (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel exitChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 2) haltRow (·.is_real)) :
    (HaltChip.exitMessage row).value = witness.publicInput.exit_code := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  apply exit_code_of_mem witness constraints balanced
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨physical, physicalMem, by simp only [real]; exact List.mem_cons_self⟩

/-- The syscall instruction's own HALT selector supplies the same public Exit binding. -/
theorem syscall_exit_code (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel exitChannel.toRaw)
    {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : row ∈ activeSystemRows (systemTable witness 3) syscallInstrsRow (·.is_real))
    (halted : row.is_halt = 1) :
    (SyscallInstrsChip.exitMessage row).value = witness.publicInput.exit_code := by
  obtain ⟨physical, physicalMem, same, _⟩ := activeSystemRows_member _ _ _ member
  apply exit_code_of_mem witness constraints balanced
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨physical, physicalMem, by simp only [same, halted]⟩

end SP1Clean.Soundness.LocalCore
