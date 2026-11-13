import SP1Clean.Soundness.TypedMemorySelectors
import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.TypedState
import SP1Clean.Model.Semantics.Truth
import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.Model.Machine.Syscall
import Mathlib.Data.Set.Basic
import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Machine.Execution
import SP1Clean.Soundness.BumpDecode

/-! # Memory-channel structure of the supported ensemble

Structural facts about the Memory channel of `sp1Ensemble`. The boundary verifier contributes
nothing. A decoded instruction row's Memory messages are, by definition, those of its actual
retained Clean interactions (`DecodedInstructionRow.producedMemoryMessages` /
`consumedMemoryMessages`), so the ensemble decomposition threads them through without a per-chip
shape sweep. The init and finalize provider tables only push and only pull, one boolean-gated
interaction per row, and a constrained padding row has no active Memory message. The byte, range
and program providers do not declare the Memory channel. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Use the field instance consistently when filtering physical interaction counts. -/
local instance memoryBalanceDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

/-! ## Generic distribution of produced/consumed messages over `flatMap` -/

section Distribution

variable {Message : TypeMap} [ProvableType Message] {channel : Channel (ZMod p) Message}

omit [Fact (2 ^ 24 < p)] in
/-- Active produced messages distribute over a `flatMap`: the produced messages of a concatenated
family are the concatenation of each block's produced messages. -/
theorem producedMessages_flatMap {α : Type*} (l : List α)
    (f : α → List (TypedInteraction channel)) :
    producedMessages (l.flatMap f) = l.flatMap fun x => producedMessages (f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, producedMessages_append, ih, List.flatMap_cons]

omit [Fact (2 ^ 24 < p)] in
/-- Active consumed messages distribute over a `flatMap`. -/
theorem consumedMessages_flatMap {α : Type*} (l : List α)
    (f : α → List (TypedInteraction channel)) :
    consumedMessages (l.flatMap f) = l.flatMap fun x => consumedMessages (f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, consumedMessages_append, ih, List.flatMap_cons]

end Distribution

/-! ## The boundary verifier contributes nothing to the Memory channel -/

/-- The public verifier contributes State, Byte and Exit traffic, with no Memory occurrence. -/
theorem witness_verifierMemoryInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedInteractionValuesWith (sp1Ensemble (p := p)).verifierOperations memoryChannel
      witness.data.publicEnvironment = [] := by
  apply List.map_eq_nil_iff.mp
  rw [typedInteractionValuesWith_raw]
  simp only [sp1Ensemble, Ensemble.verifierOperations, sp1StateVerifierProgram,
    Verifier.Program.circuitOperations, Verifier.Program.operations, Verifier.ofInteractions_values]
  simp [Operations.interactionValuesWith, sp1StateVerifierMain, circuit_norm]

/-! ## Exact Memory-channel decomposition of the whole ensemble witness -/

/-- The decoded witness Memory interactions are the flattened per-row interaction lists — the
definitional carrier of the per-row `producedMemoryMessages`/`consumedMemoryMessages`. -/
theorem decodedWitnessMemoryInteractions_eq_flatMap
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables memoryChannel =
      (decodedInstructionRows (p := p) witness.tables).flatMap
        fun decoded => decoded.interactionsWith witness.data memoryChannel := rfl

/-! ## Provider purity: the boundary tables only push (init) / only pull (finalize)

Each boundary
provider emits exactly **one** explicit, boolean-gated Memory interaction per row — the init provider a
`memoryChannel.pushIf m` (`MemoryProviderChip`), the finalize provider a `memoryChannel.pullIf m`
(`MemoryFinalizeChip`) — with `m` forced into `{0, 1}` by the inline `assertZero (m * (m - 1))` gate.
Direction is stored separately from the boolean count: the init table contributes only pushes and
the finalize table contributes only pulls. Purity therefore needs no constraint assumption. -/

/-- `MemoryProviderChip`'s range-check subcircuit declares no channels, so it emits no Memory
interaction; its `FlatOperation.interactions` filtered to `memoryChannel` is empty. -/
lemma wordRangeCheck_no_memory (offset : ℕ) (w : Var Word (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
      [Operation.subcircuit (WordRangeCheck.circuit.toSubcircuit offset w)] = [] := by
  have h := InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
    WordRangeCheck.circuit memoryChannel.toRaw (n := offset) w ([] : Operations (ZMod p))
    List.not_mem_nil List.not_mem_nil
  rwa [Operations.interactionsWith_nil] at h

/-- The init provider's boolean gate `assertZero (m * (m - 1))` forces its explicit multiplicity
input into `{0, 1}`. -/
theorem memoryInitProvider_gate_binary (input : Var MemoryProviderChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryProviderChip.main input).operations offset)) :
    Expression.eval env input.multiplicity = 0 ∨
      Expression.eval env input.multiplicity = 1 := by
  have allShallow := (constraintsHold_shallow_iff_forall_mem.mp constraints).1
  have gate := allShallow (input.multiplicity * (input.multiplicity - 1))
    (by simp only [MemoryProviderChip.main, circuit_norm, Operations.shallowConstraints,
      List.mem_cons, or_true, true_or])
  simp only [eval_sub, Expression.eval] at gate
  exact bool_of_mul_pred gate

/-- The init provider's only Memory interaction is its single `pushIf input.multiplicity`; the
range-check subcircuit contributes nothing. -/
theorem memoryInitProvider_memoryInteractions
    (input : Var MemoryProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryProviderChip.main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(pushedIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw] := by
  classical
  simp only [MemoryProviderChip.main, circuit_norm]
  rw [show List.filter (fun i => decide (i.channel = memoryChannel.toRaw))
      (FlatOperation.interactions (WordRangeCheck.circuit.toSubcircuit offset input.value).ops.toFlat)
      = [] from by
    have h := wordRangeCheck_no_memory offset input.value
    simpa [Operations.interactionsWith_subcircuit, Operations.interactionsWith_nil] using h]
  rfl

/-- Every typed Memory interaction the init-provider component emits has multiplicity equal to the
explicit multiplicity input. -/
theorem memoryInitProvider_typedShape (env : Environment (ZMod p))
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith ({ circuit := MemoryProviderChip.circuit, Assumptions := (MemoryProviderChip.circuit).Assumptions, generation := MemoryProviderChip.generation } : Component (ZMod p)).operations
      memoryChannel env) :
    i.mult = env.get (size MemoryMsg) ∧ i.raw.direction = .push := by
  have hint : ({ circuit := MemoryProviderChip.circuit, Assumptions := (MemoryProviderChip.circuit).Assumptions, generation := MemoryProviderChip.generation } : Component (ZMod p)).operations.interactionsWith
      memoryChannel.toRaw =
      [(pushedIf (channel := memoryChannel)
        (varFromOffset MemoryProviderChip.Inputs 0).multiplicity
        (varFromOffset MemoryProviderChip.Inputs 0).toMessage).toRaw] := by
    rw [Component.interactionsWith_eq, Component.rowOperations]
    exact memoryInitProvider_memoryInteractions (varFromOffset MemoryProviderChip.Inputs 0)
      (size MemoryProviderChip.Inputs)
  have hraw : i.raw ∈ (typedInteractionValuesWith
      ({ circuit := MemoryProviderChip.circuit, Assumptions := (MemoryProviderChip.circuit).Assumptions, generation := MemoryProviderChip.generation } : Component (ZMod p)).operations memoryChannel env).map
      TypedInteraction.raw := List.mem_map_of_mem hi
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map, hint] at hraw
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hraw
  constructor
  · rw [TypedInteraction.mult, hraw]
    simp only [AbstractInteraction.eval, ChannelInteraction.toRaw_mult, pushedIf_mult,
      MemoryProviderChip.Inputs.varFromOffset_multiplicity, Expression.eval, Nat.zero_add]
  · rw [hraw]
    rfl

/-- Every init-provider Memory interaction has a boolean count. -/
theorem memoryInitProvider_isBool (env : Environment (ZMod p))
    (constraints : ({ circuit := MemoryProviderChip.circuit, Assumptions := (MemoryProviderChip.circuit).Assumptions, generation := MemoryProviderChip.generation } : Component (ZMod p)).operations.ConstraintsHold env)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith ({ circuit := MemoryProviderChip.circuit, Assumptions := (MemoryProviderChip.circuit).Assumptions, generation := MemoryProviderChip.generation } : Component (ZMod p)).operations
      memoryChannel env) :
    IsBool i.mult := by
  have hmult := memoryInitProvider_typedShape env i hi
  have shallow := shallowConstraints_of_componentConstraints MemoryProviderChip.circuit env constraints
  have hbool := memoryInitProvider_gate_binary (varFromOffset MemoryProviderChip.Inputs 0)
    (size MemoryProviderChip.Inputs) env shallow
  simp only [MemoryProviderChip.Inputs.varFromOffset_multiplicity, Expression.eval,
    Nat.zero_add] at hbool
  rw [hmult.1]
  exact hbool

omit [Fact (2 ^ 24 < p)] in
/-- The finalize provider's only Memory interaction is its single explicit-multiplicity pull. -/
theorem memoryFinalizeProvider_memoryInteractions
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryFinalizeChip.main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(pulledIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw] := by
  simp only [MemoryFinalizeChip.main, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The finalize provider's boolean gate forces its explicit multiplicity input into `{0, 1}`. -/
theorem memoryFinalizeProvider_gate_binary
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryFinalizeChip.main input).operations offset)) :
    Expression.eval env input.multiplicity = 0 ∨
      Expression.eval env input.multiplicity = 1 := by
  have allShallow := (constraintsHold_shallow_iff_forall_mem.mp constraints).1
  have gate := allShallow (input.multiplicity * (input.multiplicity - 1))
    (by simp only [MemoryFinalizeChip.main, circuit_norm, Operations.shallowConstraints,
      List.mem_cons, true_or])
  simp only [eval_sub, Expression.eval] at gate
  exact bool_of_mul_pred gate

omit [Fact (2 ^ 24 < p)] in
/-- Every typed Memory interaction the finalize-provider component emits has its explicit nonnegative selector count and pull direction. -/
theorem memoryFinalizeProvider_typedShape (env : Environment (ZMod p))
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith ({ circuit := MemoryFinalizeChip.circuit, Assumptions := (MemoryFinalizeChip.circuit).Assumptions, generation := MemoryFinalizeChip.generation } : Component (ZMod p)).operations
      memoryChannel env) :
    i.mult = env.get (size MemoryMsg) ∧ i.raw.direction = .pull := by
  have hint : ({ circuit := MemoryFinalizeChip.circuit, Assumptions := (MemoryFinalizeChip.circuit).Assumptions, generation := MemoryFinalizeChip.generation } : Component (ZMod p)).operations.interactionsWith
      memoryChannel.toRaw =
      [(pulledIf (channel := memoryChannel)
        (varFromOffset MemoryFinalizeChip.Inputs 0).multiplicity
        (varFromOffset MemoryFinalizeChip.Inputs 0).toMessage).toRaw] := by
    rw [Component.interactionsWith_eq, Component.rowOperations]
    exact memoryFinalizeProvider_memoryInteractions (varFromOffset MemoryFinalizeChip.Inputs 0)
      (size MemoryFinalizeChip.Inputs)
  have hraw : i.raw ∈ (typedInteractionValuesWith
      ({ circuit := MemoryFinalizeChip.circuit, Assumptions := (MemoryFinalizeChip.circuit).Assumptions, generation := MemoryFinalizeChip.generation } : Component (ZMod p)).operations memoryChannel env).map
      TypedInteraction.raw := List.mem_map_of_mem hi
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map, hint] at hraw
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hraw
  constructor
  · rw [TypedInteraction.mult, hraw]
    simp only [AbstractInteraction.eval, ChannelInteraction.toRaw_mult, pulledIf_mult,
      MemoryFinalizeChip.Inputs.varFromOffset_multiplicity, Expression.eval, Nat.zero_add]
  · rw [hraw]
    rfl

omit [Fact (2 ^ 24 < p)] in
/-- Every finalize-provider Memory interaction has a boolean count. -/
theorem memoryFinalizeProvider_isBool (env : Environment (ZMod p))
    (constraints : ({ circuit := MemoryFinalizeChip.circuit, Assumptions := (MemoryFinalizeChip.circuit).Assumptions, generation := MemoryFinalizeChip.generation } : Component (ZMod p)).operations.ConstraintsHold env)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedInteractionValuesWith ({ circuit := MemoryFinalizeChip.circuit, Assumptions := (MemoryFinalizeChip.circuit).Assumptions, generation := MemoryFinalizeChip.generation } : Component (ZMod p)).operations
      memoryChannel env) :
    IsBool i.mult := by
  have hmult := memoryFinalizeProvider_typedShape env i hi
  have shallow :=
    shallowConstraints_of_componentConstraints MemoryFinalizeChip.circuit env constraints
  have hbool := memoryFinalizeProvider_gate_binary (varFromOffset MemoryFinalizeChip.Inputs 0)
    (size MemoryFinalizeChip.Inputs) env shallow
  simp only [MemoryFinalizeChip.Inputs.varFromOffset_multiplicity, Expression.eval,
    Nat.zero_add] at hbool
  rw [hmult.1]
  exact hbool

/-! ## Witness-level structural Memory obligations -/

omit [Fact (2 ^ 24 < p)] in
/-- The MemoryBump circuit's inline boolean gate, extracted from the shallow constraint list. -/
private theorem memoryBump_gate_binary [Fact (2 ^ 17 < p)]
    (r : Var MemoryBumpChip.Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ConstraintsHold.Shallow env ((MemoryBumpChip.main r).operations offset)) :
    (ProvableStruct.eval env r).is_real = 0 ∨ (ProvableStruct.eval env r).is_real = 1 := by
  simpa only [circuit_norm] using MemoryBumpChip.selectorBinary_of_shallow r offset env constraints

/-- Every MemoryBump row's selector is boolean, from its table constraints alone (the inline gate
is an ungated assert — no channel guarantee is needed, so this is non-circular for the memory
balance). -/
private theorem memoryBumpTable_is_real_binary
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints) :
    ∀ row ∈ (memoryBumpTable witness).table,
      (memoryBumpRow witness.data row).is_real = 0 ∨
        (memoryBumpRow witness.data row).is_real = 1 := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  intro row rowMem
  have tableConstraints : (memoryBumpTable witness).Constraints :=
    constraints _ (List.getElem_mem (memoryBumpIndex_lt_tablesLength witness))
  have rowConstraints := tableConstraints row rowMem
  rw [Table.environment, memoryBumpTable_data, memoryBumpTable_component witness] at rowConstraints
  have shallow := shallowConstraints_of_componentConstraints MemoryBumpChip.circuit
    (Environment.fromArray row witness.data) rowConstraints
  have hbool := memoryBump_gate_binary (varFromOffset MemoryBumpChip.Inputs 0)
    (size MemoryBumpChip.Inputs) (Environment.fromArray row witness.data) shallow
  rw [show (memoryBumpRow witness.data row).is_real =
      (ProvableStruct.eval (Environment.fromArray row witness.data)
        (varFromOffset MemoryBumpChip.Inputs 0 :
          Var MemoryBumpChip.Inputs (ZMod p))).is_real from by
    rw [memoryBumpRow_eq, ProvableStruct.eval_eq_eval]]
  exact hbool

/-- Every typed Memory interaction of the MemoryBump table is boolean-gated, with direction stored separately. -/
private theorem memoryBumpTable_isBool
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (memoryBumpTable witness) memoryChannel) :
    IsBool i.mult := by
  rw [memoryBumpTable_typedMemory] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  have hbool := memoryBumpTable_is_real_binary witness constraints row rowMem
  rcases List.mem_cons.mp hi with rfl | hi
  · rw [TypedInteraction.pulledIfValue_mult]
    exact hbool
  · rw [List.mem_singleton.mp hi, TypedInteraction.pushedIfValue_mult]
    exact hbool

private theorem haltTable_memory_isBool
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (haltTable witness) memoryChannel) :
    IsBool i.mult := by
  rw [haltTable_typedMemory] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  have hbool := witness_haltRows_selectorBinary witness constraints row rowMem
  have pullCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pulledIfValue memoryChannel
        (haltRow witness.data row).is_real msg →
      IsBool i.mult := by
    rintro msg rfl
    rw [TypedInteraction.pulledIfValue_mult]
    exact hbool
  have pushCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pushedIfValue memoryChannel
        (haltRow witness.data row).is_real msg →
      IsBool i.mult := by
    rintro msg rfl
    rw [TypedInteraction.pushedIfValue_mult]
    exact hbool
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl

/-- The `SyscallInstrs` table's Memory multiplicities are `{0, 1}` — the same argument as the
Halt table's, since both gate all six register interactions on the row's single boolean selector. -/
private theorem syscallInstrsTable_memory_isBool
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (i : TypedInteraction (memoryChannel (p := p)))
    (hi : i ∈ typedTableInteractionsWith (syscallInstrsTable witness) memoryChannel) :
    IsBool i.mult := by
  rw [syscallInstrsTable_typedMemory] at hi
  obtain ⟨row, rowMem, hi⟩ := List.mem_flatMap.mp hi
  have hbool := witness_syscallInstrsRows_selectorBinary witness constraints row rowMem
  have pullCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pulledIfValue memoryChannel
        (syscallInstrsRow witness.data row).is_real msg →
      IsBool i.mult := by
    rintro msg rfl
    rw [TypedInteraction.pulledIfValue_mult]
    exact hbool
  have pushCase : ∀ msg : MemoryMsg (ZMod p),
      i = TypedInteraction.pushedIfValue memoryChannel
        (syscallInstrsRow witness.data row).is_real msg →
      IsBool i.mult := by
    rintro msg rfl
    rw [TypedInteraction.pushedIfValue_mult]
    exact hbool
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl
  · exact pullCase _ rfl
  · exact pushCase _ rfl

/-- A constrained padding instruction row has no active Memory message.  This is a direct
consequence of selector booleanity and the fact that every retained Memory interaction is gated by
that selector; it is not an execution or trace-generation assumption. -/
theorem witness_paddingMemoryEmpty
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [] := by
  intro decoded decodedMem padding
  exact decoded.paddingMemoryMessages_eq_nil witness.data witness.tables decodedMem
    (decodedInstructionRow_constraints witness constraints decoded decodedMem) padding

end SP1Clean.Soundness
