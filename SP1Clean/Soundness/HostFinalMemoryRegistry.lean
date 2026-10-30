import SP1Clean.Soundness.HostHintReadLocalRecords
import SP1Clean.Soundness.FinalMemoryChecks

/-! # Static registry of the complete-memory host inventory

The installed host registry and both target validators keep distinct canonical names, and the
validators have a proved static host-resource interface. The source-backed host proofs are stated
over this one inventory, so these facts sit below them.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalNamesLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The complete physical host inventory has distinct canonical names before receipt wrapping. -/
abbrev UniqueNames (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot)
    (others : List (HostLocalHandoff.Receiver (p := p))) (resources : List (Component (ZMod p))) : Prop :=
  ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: others).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ (resources ++ FinalMemoryChecks.checkTables target)))).map
      (·.circuit.name)).Nodup

/-- The concrete host registry and both target validators have distinct canonical names. -/
theorem source_unique_names (image : ProgramImage) (source : ExecutionSnapshot) (target : MemorySnapshot) :
    UniqueNames (p := p) image source target HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) := by
  let original := HostLocalCore.tables (p := p) image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources source.host.io.hints))
  have split : ((HostLocalCore.tables (p := p) image source
      ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++
          FinalMemoryChecks.checkTables target)))).map (·.circuit.name)) =
      original.map (·.circuit.name) ++ (FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name) := by
    simp only [original, HostLocalCore.tables_names, List.map_append, List.append_assoc]
  rw [UniqueNames, split, List.nodup_append]
  refine ⟨HostHintReadLocal.source_unique_names image source source.host.io.hints,
    ?_, ?_⟩
  · simp only [FinalMemoryChecks.checkTables, List.map_cons, List.map_nil,
      StaticTable.component, StaticTable.provider, FinalRegisterValue.membership]
    exact of_decide_eq_true rfl
  · have fresh : (original.map (·.circuit.name)).all
        (fun name => !((FinalMemoryChecks.checkTables (p := p) target).map (·.circuit.name)).contains name) = true := by
      simp only [original, HostLocalCore.tables_names, ProtectedLocalCore.tables_names,
        LocalCore.tables, LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil,
        SnapshotMemoryEnsemble.registerMembership, StaticTable.component, StaticTable.provider,
        MemorySnapshot.registerTable, StaticTable.ofRows,
        FinalMemoryChecks.checkTables, FinalRegisterValue.membership]
      rfl
    intro a old b added same
    have absent := List.all_eq_true.mp fresh a old
    rw [List.contains_iff_mem.mpr (same.symm ▸ added)] at absent
    exact Bool.noConfusion absent

omit [Fact (2 ^ 25 < p)] in
/-- A component without a Byte requirement discharges its Byte requirement vacuously. -/
theorem not_required (component : Component (ZMod p))
    (quiet : (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = false)
    (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    component.operations.ChannelRequirements byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _ (component.inChannelsOrRequirements_of_constraints env checked)
  intro member
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  change (component.circuit.channelsWithRequirements.map RawChannel.name).contains "SP1Byte" = true at present
  rw [quiet] at present
  contradiction

/-- A name check over the validators shows they never use a channel. -/
theorem checks_silent (target : MemorySnapshot) (channel : RawChannel (ZMod p))
    (quiet : (FinalMemoryChecks.checkTables (p := p) target).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true) :
    ∀ component ∈ FinalMemoryChecks.checkTables target, channel ∉ component.circuit.channels := by
  intro component member used
  have silent := List.all_eq_true.mp quiet component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
  contradiction

/-- The target consumers have a proved static host-resource interface. -/
theorem targetInterface (target : MemorySnapshot)
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    (interface : HostHintReadLocal.ExtensionInterface others resources) :
    HostHintReadLocal.ExtensionInterface others (resources ++ FinalMemoryChecks.checkTables target) := by
  apply interface.appendResources
  · constructor
    · intro component member env checked
      simp only [FinalMemoryChecks.checkTables, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact not_required _ (by rfl) env checked
    · exact checks_silent target stateChannel.toRaw (by rfl)
  · exact checks_silent target HostCallChip.channel.toRaw (by rfl)
  · exact checks_silent target HintReadWordChip.stateChannel.toRaw (by rfl)

/-- The concrete host registry with both target validators has a proved static interface. -/
theorem sourceInterface (hints : List Bytes) (target : MemorySnapshot) :
    HostHintReadLocal.ExtensionInterface (HostCallReceivers.available (p := p))
      (HostHintReadLocal.sourceResources hints ++ FinalMemoryChecks.checkTables target) :=
  targetInterface target (HostHintReadLocal.source_interface hints)

end SP1Clean.Soundness.HostFinalMemory
