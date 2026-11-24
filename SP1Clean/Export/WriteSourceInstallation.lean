import SP1Clean.Export.WriteSourceRegistry

/-! # Native WRITE publishers in the supervisor ensemble -/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness WriteProbe WriteProbe.AccessInventory

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod SP1Prime))

private theorem verifier_ne (name stem : String) (endName : name.toList.getLast? ≠ some '_')
    (ens : Ensemble (ZMod SP1Prime) SP1PublicIO) : name ≠ (VerifierChannel.channel stem ens).name := by
  intro same
  apply endName
  rw [same]
  change (VerifierChannel.channelName stem ens).toList.getLast? = _
  simp [VerifierChannel.channelName, List.replicate_succ']

/-- Protocol names are disjoint from the supervisor if they are absent from the underlying
registry and have a different suffix from all generated verifier-check names. -/
theorem fresh_of_registry (name : String) (ending : name.toList.getLast? ≠ some '_')
    (unlisted : name ∉ (HostLocalCore.registry (p := SP1Prime) image source
      (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels target.sail.memorySnapshot)).map RawChannel.name) :
    name ∉ ((base image source target final).channels.map RawChannel.name) := by
  simp only [base, HostObserved.ensemble, ClosedVerifier.withInteractions, HostObserved.producers,
    HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble, PublicVerifier.install,
    HostFinalMemory.ensemble, ClosedVerifier.install, HostFinalMemory.withReceipts,
    HostFinalMemory.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent,
    HostFinalMemory.base, HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble,
    HostLocalHandoff.ensemble, HostLocalCore.ensemble, HostLocalCore.baseEnsemble, List.map_append,
    List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  simp only [unlisted, false_or, not_or]
  exact ⟨⟨⟨verifier_ne name _ ending _, verifier_ne name _ ending _⟩, verifier_ne name _ ending _⟩,
    verifier_ne name _ ending _⟩

private theorem fresh : (readbackChannel (p := SP1Prime)).name ∉ ((base image source target final).channels.map RawChannel.name) := by
  apply fresh_of_registry image source target final _ (by decide)
  simp only [HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels,
    HostFinalMemory.sourceChannels, HostFinalMemory.receiptChannels, HostFinalMemory.externalChannels,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    StaticTable.channel, StaticTable.ofRows, MemorySnapshot.registerTable, ProgramImage.writePermissionTable,
    InitialMemoryLookup.membership, FinalRegisterValue.membership, Channel.toRaw_name]
  exact of_decide_eq_true rfl

private theorem mapNames (tables : List (Component (ZMod SP1Prime)))
    (same : ∀ i old, tables[i]? = some old → (decorate i old).circuit.name = old.circuit.name) :
    (tables.mapIdx decorate).map (·.circuit.name) = tables.map (·.circuit.name) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [List.getElem_map, List.getElem_map, List.getElem_mapIdx]
    exact same i _ (List.getElem?_eq_getElem _)

attribute [local irreducible] base

/-- Register every physical source under the dedicated native read-back protocol before
connecting the counted supplier. The verifier still owns the public program and snapshots. -/
def withSources : Ensemble (ZMod SP1Prime) SP1PublicIO :=
  let old := base image source target final
  { old with
    tables := old.tables.mapIdx decorate
    channels := readbackChannel.toRaw :: old.channels
    unique_channel_names := List.nodup_cons.mpr ⟨fresh image source target final, old.unique_channel_names⟩
    unique_names := (mapNames old.tables (sameName image source target final)) ▸ old.unique_names
    verifier_channels := fun _ used => List.mem_cons_of_mem _ (old.verifier_channels used)
    tables_channels := by
      intro table member ch used
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
      rw [List.getElem_mapIdx] at used
      unfold decorate at used
      cases found : sourceAt i with
      | none =>
        rw [found] at used
        exact List.mem_cons_of_mem _ (old.tables_channels _ (List.getElem_mem ..) used)
      | some id =>
        rw [found] at used
        rcases publisher_channels id used with prior | rfl
        · have installed := original_at image source target final id
          exact List.mem_cons_of_mem _ (old.tables_channels _ (List.mem_of_getElem? installed) prior)
        · exact List.Mem.head _ }

/-- Decorate the existing table order, preserving the original public verifier and names. -/
theorem tables_eq : (withSources image source target final).tables =
    (base image source target final).tables.mapIdx decorate := rfl

theorem names_eq : (withSources image source target final).tables.map (·.circuit.name) =
    (base image source target final).tables.map (·.circuit.name) :=
  mapNames _ (sameName image source target final)

theorem channels_eq : (withSources image source target final).channels =
    readbackChannel.toRaw :: (base image source target final).channels := rfl

theorem verifier_eq : (withSources image source target final).verifier =
    (base image source target final).verifier := rfl

/-- The installed physical component at each canonical source position is its actual publisher. -/
theorem publisher_at (id : Source) :
    (withSources image source target final).tables[position id]? = some (publisher id) := by
  change ((base image source target final).tables.mapIdx decorate)[position id]? = _
  rw [List.getElem?_mapIdx, original_at, Option.map_some]
  unfold decorate
  rw [sourceAt_position]
  rfl

end SP1Clean.Export.WriteSourceRegistry
