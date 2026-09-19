import SP1Clean.Soundness.HostLocalCoreMemory
import SP1Clean.Soundness.LocalCoreRows

/-! # The full host Memory interior in execution-row form

The physical wrapper adds an x12 pair to the instruction prefix, and appended components retain
their complete Memory ledgers. Separating these contributions is a permutation: wrapper rows
interleave old and new accesses. No host access, disabled interaction, or duplicate occurrence
is discarded, and no Memory balance is projected to the smaller local assembly.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

/-- Every physical wrapper's additional pair, including its zero-multiplicity padding. -/
def wrapperMemory (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  ((hostCallTable witness).table.map (hostCallTable witness).environment).flatMap fun env =>
    [TypedInteraction.pulledIfValue memoryChannel (HostCallProjection.extraRead env).is_real
      (HostCallProjection.extraRead env).prior,
     TypedInteraction.pushedIfValue memoryChannel (HostCallProjection.extraRead env).is_real
      (HostCallProjection.extraRead env).pushed]

/-- The actual appended component ledgers, without imposing a particular handler registry. -/
noncomputable def auxiliaryMemory (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    List (TypedInteraction (memoryChannel (p := p))) :=
  (auxiliaryTables witness).flatMap (typedTableInteractionsWith · memoryChannel)

private theorem local_length (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (localWitness witness).tables.length = 59 := by
  rw [← (localWitness witness).same_length]
  exact LocalCore.tables_length image source

private theorem extended_length (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    60 ≤ witness.tables.length := by
  rw [← witness.same_length]
  change 60 ≤ (tables image source auxiliary).length
  rw [tables_length]
  omega

private theorem table_memory_original (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (index : Fin 59) (notWrapper : index.val ≠ 58) :
    typedTableInteractionsWith ((localWitness witness).tables[index.val]'(by rw [local_length]; exact index.isLt))
        memoryChannel =
      typedTableInteractionsWith (witness.tables[index.val]'(by have := extended_length witness; omega)) memoryChannel := by
  rw [localWitness_table]
  apply List.map_injective_iff.mpr TypedInteraction.raw_injective
  simp only [typedTableInteractionsWith_raw]
  apply Table.withComponent_interactions
  rw [← witness.same_circuits]
  change _ = ((tables image source auxiliary)[index.val]'(by rw [tables_length]; omega)).operations.interactionsWith _
  rw [core_component image source auxiliary index, if_neg (Ne.symm notWrapper)]
  exact ((ProtectedLocalCore.component_projection (p := p) image source index).2.2 memoryChannel.toRaw
    (by simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw])).symm

private theorem before_wrapper (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (((localWitness witness).tables.drop 6).take 52).flatMap (typedTableInteractionsWith · memoryChannel) =
      ((witness.tables.drop 6).take 52).flatMap (typedTableInteractionsWith · memoryChannel) := by
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, local_length]
    have := extended_length witness
    omega
  · intro index left right
    have bound : index < 52 := by
      simp only [List.length_map, List.length_take, List.length_drop, local_length] at left
      omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    exact table_memory_original witness ⟨6 + index, by omega⟩ (by dsimp only; omega)

private theorem original_wrapper (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (LocalCore.systemTable (localWitness witness) 3) =
      (hostCallTable witness).withComponent HostCallProjection.original := by
  change (localWitness witness).tables[58]'_ = _
  rw [localWitness_table witness ⟨58, by decide⟩]
  rfl

private theorem wrapper_memory_perm (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints) :
    (typedTableInteractionsWith (hostCallTable witness) memoryChannel).Perm
      (typedTableInteractionsWith (LocalCore.systemTable (localWitness witness) 3) memoryChannel ++
        wrapperMemory witness) := by
  rw [original_wrapper, typedTableInteractionsWith, typedTableInteractionsWith, wrapperMemory, List.flatMap_map]
  have values : (hostCallTable witness).table.flatMap
      (fun physical => typedInteractionValuesWith (hostCallTable witness).component.operations memoryChannel
        ((hostCallTable witness).environment physical)) =
      (hostCallTable witness).table.flatMap (fun physical =>
        typedInteractionValuesWith HostCallProjection.original.operations memoryChannel
          ((hostCallTable witness).environment physical) ++
        [TypedInteraction.pulledIfValue memoryChannel
          (HostCallProjection.extraRead ((hostCallTable witness).environment physical)).is_real
          (HostCallProjection.extraRead ((hostCallTable witness).environment physical)).prior,
         TypedInteraction.pushedIfValue memoryChannel
          (HostCallProjection.extraRead ((hostCallTable witness).environment physical)).is_real
          (HostCallProjection.extraRead ((hostCallTable witness).environment physical)).pushed]) := by
    apply List.flatMap_congr
    intro physical member
    have checked := constraints _ (hostCallTable_mem witness) physical member
    rw [hostCallTable_component] at checked ⊢
    exact wrapper_memory_interactions _ checked
  rw [values]
  exact (List.flatMap_append_perm _ _ _).symm

private theorem permission_memory_nil (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    typedTableInteractionsWith (witness.tables[59]'(by have := extended_length witness; omega)) memoryChannel = [] := by
  have component : (witness.tables[59]'(by have := extended_length witness; omega)).component =
      ⟨WritePermissionProvider.circuit image⟩ := by
    rw [← witness.same_circuits]
    change (tables image source auxiliary)[59]'(by rw [tables_length]; omega) = _
    simp only [tables]
    rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; decide),
      List.getElem_set_ne (by decide)]
    rfl
  apply (List.map_eq_nil_iff (f := TypedInteraction.raw)).mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [component]
  change memoryChannel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
  simp [memoryChannel, WritePermissionProvider.channel, Channel.toRaw]

/-- The complete interior is the original instruction/refresh ledger plus all actual host
accesses. The permutation preserves complete typed interactions, including disabled pairs. -/
theorem memoryInterior_perm (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (constraints : witness.Constraints) :
    (memoryInterior witness).Perm
      (LocalCore.memoryInterior (localWitness witness) ++ wrapperMemory witness ++ auxiliaryMemory witness) := by
  have fullSplit : witness.tables.drop 58 = hostCallTable witness ::
      witness.tables[59]'(by have := extended_length witness; omega) :: witness.tables.drop 60 := by
    rw [List.drop_eq_getElem_cons (by have := extended_length witness; omega),
      List.drop_eq_getElem_cons (by have := extended_length witness; omega)]
    rfl
  have originalSplit : (localWitness witness).tables.drop 58 = [LocalCore.systemTable (localWitness witness) 3] := by
    rw [List.drop_eq_getElem_cons (by rw [local_length]; decide),
      List.drop_eq_nil_of_le (by rw [local_length])]
    rfl
  rw [memoryInterior, NativeCore.flatMap_split witness.tables _ 6 52, fullSplit,
    List.flatMap_cons, List.flatMap_cons, permission_memory_nil, List.nil_append]
  rw [LocalCore.memoryInterior, NativeCore.flatMap_split (localWitness witness).tables _ 6 52,
    originalSplit, List.flatMap_cons, List.flatMap_nil, List.append_nil, before_wrapper]
  simpa only [List.append_assoc, auxiliaryMemory, auxiliaryTables] using
    ((wrapper_memory_perm witness constraints).append_right
      ((witness.tables.drop 60).flatMap (typedTableInteractionsWith · memoryChannel))).append_left
        (((witness.tables.drop 6).take 52).flatMap (typedTableInteractionsWith · memoryChannel))

end SP1Clean.Soundness.HostLocalCore
