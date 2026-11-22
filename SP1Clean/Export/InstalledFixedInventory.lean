import SP1Clean.Export.FixedRamCapacity
import SP1Clean.Export.FixedImageCapacity
import SP1Clean.Export.FixedHintCapacity
import SP1Clean.Export.InstalledCapacity

/-! # Preallocated providers of the installed ensemble

The physical inventory determines each provider and its row width. Ordinary receipt installation
only replaces demand components. The fixed clock terminal emits two interactions on one channel.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Soundness Semantics.HintQueue

private def originalTables (ctx : Context) : List (Component Fp) := (HostFinalMemory.Installed ctx.image ctx.source ctx.target (publicCursor ctx)).tables
private theorem observed (ctx : Context) : (assembly ctx).tables =
   (originalTables ctx).mapIdx HostOrdinaryReceipts.replace ++ [CommitmentDeclaration.source ctx.commitments, HostHintQueueTerminal.component (publicCursor ctx)] := by
  rw [tables_eq]
  simp only [FixedHintAssembly.withoutCommitments, Shard.installed, HostObserved.ensemble, ClosedVerifier.withInteractions, HostObserved.producers, HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble, PublicVerifier.install, HostFinalMemory.Installed, originalTables, publicCursor, Context.withClock]
private def fixedOld (ctx : Context) : List (Component Fp) :=
 [FixedProgramProvider.Preprocessed.component ctx.image, SnapshotMemoryEnsemble.registerMembership ctx.source.sail.memorySnapshot,
  SnapshotMemoryEnsemble.ramMembership ctx.source.sail.memorySnapshot, WritePermissionProvider.membershipComponent ctx.image,
  HostHintQueue.source ctx.source.host.io.hints, HostHintQueue.sourceWord ctx.source.host.io.hints,
  (FinalRegisterValue.membership ctx.target.sail.memorySnapshot).component (FinalRegisterValue.membership_height_lt_uint64 ctx.target.sail.memorySnapshot),
  (InitialMemoryLookup.membership ctx.target.sail.memory (2^48) "sp1.native.target_memory").component (InitialMemoryLookup.membership_height_lt_uint64 ctx.target.sail.memory "sp1.native.target_memory")]
/-- Keep precisely the components whose row counts are fixed by the verifier. -/
def asFixed (c : Component Fp) : Option (Component Fp) := match c.generation with | .preallocated _ => some c | _ => none
private theorem original_fixed (ctx : Context) : (originalTables ctx).filterMap asFixed = fixedOld ctx := by
  repeat' first | apply congrArg₂ List.cons | rfl
private theorem ordinary_original (ctx : Context) (i : Fin 25) (bound : 7 + i.val < (originalTables ctx).length) : asFixed ((originalTables ctx).get ⟨7 + i.val, bound⟩) = none := by
  let _ := HostFinalMemory.source_registration (p := SP1Prime) ctx.image ctx.source ctx.target.sail.memorySnapshot
  have key := HostOrdinaryReceipts.original_component (p := SP1Prime) (image := ctx.image) (source := ctx.source)
    (target := ctx.target) (final := publicCursor ctx) (others := HostCallReceivers.available)
    (resources := HostHintReadLocal.sourceResources ctx.source.host.io.hints)
    (channels := HostFinalMemory.sourceChannels ctx.target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names ..) i
  simp only [HostSailBoundary.ensemble, PublicVerifier.install] at key
  unfold originalTables HostFinalMemory.Installed
  rw [List.get_eq_getElem, key]
  generalize InstructionChipId.all[i.val]'(by rw [InstructionChipId.all_length]; exact i.isLt) = id
  cases id <;> rfl
private theorem ordinary_new (idx : SP1Clean.InstructionChipId) : asFixed (ProtectedOrdinaryReceipt.component idx) = none := by
  cases idx <;> rfl
private theorem reordered (ctx : Context) : ((originalTables ctx).mapIdx HostOrdinaryReceipts.replace).map asFixed = (originalTables ctx).map asFixed := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_mapIdx]
    by_cases inside : 7 ≤ i ∧ i < 32
    · rw [HostOrdinaryReceipts.replace, dite_eq_left inside, ordinary_new]
      let idx : Fin 25 := ⟨i - 7, by omega⟩
      have atIdx : 7 + idx.val = i := by dsimp [idx]; omega
      have relevant := ordinary_original ctx idx (by rw [atIdx]; simpa using hj)
      simpa only [List.get_eq_getElem, atIdx] using relevant.symm
    · simp only [HostOrdinaryReceipts.replace, dite_eq_right inside]

/-- The ten preallocated components in physical order. -/
def fixedTables (ctx : Context) : List (Component Fp) := fixedOld ctx ++
  [CommitmentDeclaration.source ctx.commitments, HostHintQueueTerminal.component (publicCursor ctx)]

/-- Filtering the actual installed inventory by its Clean generation mode recovers this complete list. -/
theorem preallocated_tables (ctx : Context) : (assembly ctx).tables.filterMap asFixed = fixedTables ctx := by
  calc
    _ = ((originalTables ctx).mapIdx HostOrdinaryReceipts.replace).filterMap asFixed ++
      ([CommitmentDeclaration.source ctx.commitments, HostHintQueueTerminal.component (publicCursor ctx)] : List (Component Fp)).filterMap asFixed := by
        rw [observed, List.filterMap_append]
    _ = _ := by
        have before := congrArg (List.filterMap id) (reordered ctx)
        simp only [List.filterMap_map, Function.id_comp] at before
        rw [before]
        exact congrArg₂ List.append (original_fixed ctx) rfl

/-- Native height of a preallocated row block, or zero for a demand component. -/
def fixedHeight (c : Component Fp) : ℕ := match c.generation with | .preallocated m => m.height.toNat | _ => 0
/-- Literal registered channel names emitted by one physical row, with repetitions. -/
def rowChannelNames (c : Component Fp) : List String := c.operations.interactions.map (·.channel.name)
/-- The exact public heights of all ten verifier-fixed tables. -/
theorem fixed_heights (ctx : Context) : (fixedTables ctx).map fixedHeight =
  [FixedProgramProvider.Preprocessed.height (p := SP1Prime) ctx.image, 32,
   (InitialMemoryLookup.membership (p := SP1Prime) ctx.source.sail.memory (2 ^ 48) "sp1.native.initial_memory").height,
   (ctx.image.writePermissionTable (p := SP1Prime)).height, (sourceTable (p := SP1Prime) ctx.source.host.io.hints).height,
   (HostHintQueue.sourceWordInventory (p := SP1Prime) ctx.source.host.io.hints).height, 32,
   (InitialMemoryLookup.membership (p := SP1Prime) ctx.target.sail.memory (2 ^ 48) "sp1.native.target_memory").height, 16, 1] := by
  repeat' first | apply congrArg₂ List.cons | rfl
  · change 2 ^ Nat.clog 2 (ctx.source.sail.memorySnapshot.registerTable (p := SP1Prime)).length = _
    rw [MemorySnapshot.registerTable_length]; decide
  · change 2 ^ Nat.clog 2 (ctx.target.sail.memorySnapshot.registerTable (p := SP1Prime)).length = _
    rw [MemorySnapshot.registerTable_length]; decide
  · change 2 ^ Nat.clog 2 (CommitmentDeclaration.table (p := SP1Prime) ctx.commitments).length = _
    simp only [CommitmentDeclaration.table, StaticTable.ofRows, CommitmentDeclaration.rows, List.length_append, List.length_ofFn]
    decide
private theorem range_empty (input : Expression Fp) (offset : ℕ) :
    FlatOperation.interactions ((Gadgets.ToBits.rangeCheck 24 (by decide : 2 ^ 24 < SP1Prime)).toSubcircuit offset input).ops.toFlat = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro interaction member
  have empty := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck 24 (by decide : 2 ^ 24 < SP1Prime)) interaction.channel (n := offset) input List.not_mem_nil List.not_mem_nil
  have retained : interaction ∈ (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck 24 (by decide : 2 ^ 24 < SP1Prime)).toSubcircuit offset input).ops.toFlat).filter (fun i => decide (i.channel = interaction.channel)) := List.mem_filter.mpr ⟨member, show decide (interaction.channel = interaction.channel) = true by simp⟩
  rw [empty] at retained
  contradiction

/-- Each fixed provider charges its own named channel. The final clock row emits twice. -/
theorem fixed_rowChannels (ctx : Context) : (fixedTables ctx).map rowChannelNames =
 [[(Channels.programChannel (p := SP1Prime)).name], [(ctx.source.sail.memorySnapshot.registerTable (p := SP1Prime)).channel.name],
 [(InitialMemoryLookup.membership (p := SP1Prime) ctx.source.sail.memory (2 ^ 48) "sp1.native.initial_memory").channel.name],
 [(ctx.image.writePermissionTable (p := SP1Prime)).channel.name], [(HostHintQueue.nodeChannel (p := SP1Prime)).name], [(HostHintQueue.wordChannel (p := SP1Prime)).name],
 [(FinalRegisterValue.membership (p := SP1Prime) ctx.target.sail.memorySnapshot).channel.name],
 [(InitialMemoryLookup.membership (p := SP1Prime) ctx.target.sail.memory (2 ^ 48) "sp1.native.target_memory").channel.name],
 [(CommitmentDeclaration.channel (p := SP1Prime)).name], [(HostHintQueue.stateChannel (p := SP1Prime)).name, (HostHintQueue.stateChannel (p := SP1Prime)).name]] := by
  repeat' first | apply congrArg₂ List.cons | rfl
  · rw [rowChannelNames, Component.interactions_eq]
    change ((((FixedProgramProvider.Preprocessed.circuit ctx.image).main (varFromOffset FixedProgramProvider.Preprocessed.Input 0)).operations (size FixedProgramProvider.Preprocessed.Input)).interactions.map _) = _
    rw [FixedProgramProvider.Preprocessed.main_interactions]; rfl
  all_goals simp [rowChannelNames, Component.interactions_eq, Component.rowOperations, HostHintQueueTerminal.component, HostHintQueueTerminal.circuit, HostHintQueueTerminal.main, SnapshotMemoryEnsemble.registerMembership, SnapshotMemoryEnsemble.ramMembership, WritePermissionProvider.membershipComponent, HostHintQueue.source, HostHintQueue.sourceWord, CommitmentDeclaration.source, StaticTable.component, StaticTable.provider, StaticTable.payloadComponent, StaticTable.payloadProvider, circuit_norm]
  · rfl
  · simp only [range_empty, List.map_nil, List.nil_append]

end SP1Clean.Export.InstalledAssembly
