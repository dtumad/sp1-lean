import SP1Clean.Soundness.HostLocalCore
import SP1Clean.Soundness.LocalCoreChannels

/-! # New private protocols on the complete host-enabled local ledger

The retained verifier and 59 non-wrapper components are silent on every new private channel.
Their silence follows from the local channel inventory and the protected store projections.
Only the physical syscall wrapper and appended auxiliary tables can contribute. This exact
ledger split preserves padding and the original characteristic count bound.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

def auxiliaryTables (witness : EnsembleWitness (ensemble image source auxiliary channels)) :=
  witness.tables.drop 60

/-- Auxiliary tables retain the exact registered component inventory and order. -/
theorem auxiliaryTables_components (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    (auxiliaryTables witness).map (·.component) = auxiliary := by
  simp only [auxiliaryTables, List.map_drop, witness.tables_map_component, ensemble, tables]
  rw [List.drop_left' (by simp only [List.length_set, ProtectedLocalCore.tables_length])]

private theorem prefix_length (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    60 ≤ witness.tables.length := by
  rw [← witness.same_length]
  change 60 ≤ (tables image source auxiliary).length
  rw [tables_length]
  omega

private theorem prefixTable_silent (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (channel : RawChannel (ZMod p)) (fresh : channel ∉ (LocalCore.ensemble (p := p) image source).channels)
    (permission : channel ≠ WritePermissionProvider.channel.toRaw)
    (index : Fin 60) (notWrapper : index.val ≠ 58) :
    (witness.tables[index.val]'(by have := prefix_length witness; omega)).interactionsWith channel = [] := by
  by_cases old : index.val < 59
  · let original := (LocalCore.tables (p := p) image source)[index.val]'(by
      rw [LocalCore.tables_length]; exact old)
    have component : (witness.tables[index.val]'(by have := prefix_length witness; omega)).component =
        (ProtectedLocalCore.tables image source)[index.val]'(by rw [ProtectedLocalCore.tables_length]; exact index.isLt) := by
      rw [← witness.same_circuits]
      exact (core_component image source auxiliary ⟨index.val, old⟩).trans (if_neg (Ne.symm notWrapper))
    have silent := Table.interactionsWith_nil_of_channel_not_mem
      (table := (witness.tables[index.val]'(by have := prefix_length witness; omega)).withComponent original)
      (channel := channel) (fun used => fresh
        (LocalCore.component_channels_subset image source original
          (List.mem_cons_of_mem _ (show original ∈ LocalCore.tables image source from List.getElem_mem _)) used))
    rw [Table.withComponent_interactions _ original channel (by
      rw [component]
      exact ((ProtectedLocalCore.component_projection (p := p) image source ⟨index.val, old⟩).2.2 channel permission).symm)] at silent
    exact silent
  · have last : index.val = 59 := by omega
    have component : (witness.tables[index.val]'(by have := prefix_length witness; omega)).component = ⟨WritePermissionProvider.circuit image⟩ := by
      rw [← witness.same_circuits]
      change (tables image source auxiliary)[index.val]'(by rw [tables_length]; omega) = _
      simp only [tables]
      rw [List.getElem_append_left (by simp only [List.length_set, ProtectedLocalCore.tables_length]; exact index.isLt),
        List.getElem_set_ne (Ne.symm notWrapper)]
      simp only [last]
      rfl
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [component]
    change channel ∉ [WritePermissionProvider.channel.toRaw]
    simpa only [List.mem_singleton] using permission

/-- A fresh protocol's complete ledger comes only from the installed wrapper and actual auxiliaries. -/
theorem interactions_split_new (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (channel : RawChannel (ZMod p)) (fresh : channel ∉ (LocalCore.ensemble (p := p) image source).channels)
    (permission : channel ≠ WritePermissionProvider.channel.toRaw) :
    witness.interactionsWith channel = (hostCallTable witness).interactionsWith channel ++
      (auxiliaryTables witness).flatMap (·.interactionsWith channel) := by
  have verifierSilent : witness.verifierTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    exact fun used => fresh (LocalCore.component_channels_subset image source _ (List.mem_cons_self ..) used)
  rw [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons, verifierSilent, List.nil_append]
  have split := List.take_append_drop 60 witness.tables
  rw [← split, List.flatMap_append]
  congr 1
  have length := prefix_length witness
  have prefixTables : witness.tables.take 60 = List.ofFn (fun index : Fin 60 =>
      witness.tables[index.val]'(by omega)) := by
    apply List.ext_getElem
    · simp only [List.length_take, Nat.min_eq_left length, List.length_ofFn]
    · intro index hi hj
      simp only [List.getElem_take, List.getElem_ofFn]
  rw [prefixTables]
  have actual : (List.ofFn fun index : Fin 60 =>
      (witness.tables[index.val]'(by omega)).interactionsWith channel) =
      List.ofFn (fun index : Fin 60 => if index.val = 58 then (hostCallTable witness).interactionsWith channel else []) := by
    apply congrArg List.ofFn
    funext index
    by_cases same : index.val = 58
    · simp only [same, ↓reduceIte, hostCallTable]
    · rw [if_neg same]
      exact prefixTable_silent witness channel fresh permission index same
  simp only [List.flatMap, List.map_ofFn, Function.comp_def]
  rw [actual]
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.reduceEqDiff,
    ↓reduceIte, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil]

/-- HostCall is a fresh private channel of the native extension. -/
theorem hostCall_fresh : HostCallChip.channel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels := by
  intro member
  have names := List.mem_map_of_mem (f := RawChannel.name) member
  simp [LocalCore.ensemble, sp1Ensemble_channels, OrderedBoundary.channel,
    SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName, HostCallChip.channel,
    stateChannel, memoryChannel, byteChannel, programChannel, exitChannel, syscallChannel,
    publicValuesChannel, Channel.toRaw] at names

/-- The whole HostCall ledger, including the unique physical producer position. -/
theorem hostCall_interactions (witness : EnsembleWitness (ensemble image source auxiliary channels)) :
    witness.interactionsWith HostCallChip.channel.toRaw =
      (hostCallTable witness).interactionsWith HostCallChip.channel.toRaw ++
        (auxiliaryTables witness).flatMap (·.interactionsWith HostCallChip.channel.toRaw) :=
  interactions_split_new witness HostCallChip.channel.toRaw hostCall_fresh
    (by simp [HostCallChip.channel, WritePermissionProvider.channel, Channel.toRaw])

end SP1Clean.Soundness.HostLocalCore
