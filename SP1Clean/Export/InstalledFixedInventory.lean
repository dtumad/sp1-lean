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

private theorem original_length (ctx : Context) : (originalTables ctx).length = 98 := by
  have total := tables_length ctx
  rw [observed, List.length_append, List.length_mapIdx] at total
  change (originalTables ctx).length + 2 = 100 at total
  omega

/-- Every family of the typed instruction registry occupies an actual protected receipt slot
between physical table indices seven and 31. -/
theorem ordinary_receipt_registered (ctx : Context) (id : InstructionChipId) :
    ProtectedOrdinaryReceipt.component id ∈ (assembly ctx).tables := by
  obtain ⟨i, inRange, selected⟩ := List.getElem_of_mem (InstructionChipId.mem_all id)
  have index : i < 25 := InstructionChipId.all_length ▸ inRange
  rw [observed]
  apply List.mem_append_left
  have member := List.getElem_mem (l := (originalTables ctx).mapIdx HostOrdinaryReceipts.replace)
    (n := 7 + i) (by rw [List.length_mapIdx, original_length]; omega)
  rw [List.getElem_mapIdx, HostOrdinaryReceipts.replace, dite_eq_left (show 7 ≤ 7 + i ∧ 7 + i < 32 by omega)] at member
  simpa only [Nat.add_sub_cancel_left, selected] using member

private theorem protocol_at (ctx : Context) (i : ℕ) (lower : 63 ≤ i) (upper : i < 94) :
    (assembly ctx).tables[i]? =
      (((HostHintReadHandoff.receiver :: HostCallReceivers.available (p := SP1Prime)).map (·.component)) ++
        (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources ctx.source.host.io.hints))[i - 63]? := by
  rw [observed, List.getElem?_append_left (by rw [List.length_mapIdx]; rw [original_length]; omega),
    List.getElem?_mapIdx]
  have untouched : HostOrdinaryReceipts.replace (p := SP1Prime) i = id := by
    funext table
    simp [HostOrdinaryReceipts.replace, show ¬ (7 ≤ i ∧ i < 32) by omega]
  rw [untouched, Option.map_id_fun]
  simp only [originalTables, HostFinalMemory.Installed, HostFinalMemory.tables_eq,
    List.getElem?_set_ne (show 4 ≠ i by omega), List.getElem?_set_ne (show 3 ≠ i by omega),
    List.getElem?_set_ne (show 57 ≠ i by omega)]
  rw [List.getElem?_append_left (by rw [HostFinalMemory.prefix_length]; change i < 66 + 20 + 8; omega),
    HostFinalMemory.beforeChecks, HostLocalCore.tables,
    List.getElem?_append_right (by rw [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.length_set, ProtectedLocalCore.tables_length]
  rfl

/-- The registered handler and both padded word components survive ordinary-receipt replacement. -/
theorem hint_read_slots (ctx : Context) :
    (assembly ctx).tables[63]? = some HostHintReadCoverage.handler ∧
    (assembly ctx).tables[84]? = some (HintReadCoverage.component false) ∧
    (assembly ctx).tables[85]? = some (HintReadCoverage.component true) := by
  constructor
  · rw [protocol_at ctx 63 (by decide) (by decide)]; rfl
  constructor
  · rw [protocol_at ctx 84 (by decide) (by decide)]; rfl
  · rw [protocol_at ctx 85 (by decide) (by decide)]; rfl

/-- The observation consumer and all three terminal modes are members of the actual
installed inventory. Their physical order matches the constructed four-table witness. -/
theorem observation_registered (ctx : Context) :
    Soundness.OrdinaryObservation.consumer ∈ (assembly ctx).tables ∧
      ∀ mode, Soundness.OrdinaryObservation.terminalComponent mode ∈ (assembly ctx).tables := by
  constructor
  · apply List.mem_of_getElem? (i := 90)
    rw [protocol_at ctx 90 (by decide) (by decide)]
    rfl
  · intro mode
    cases mode with
    | empty =>
      apply List.mem_of_getElem? (i := 91)
      rw [protocol_at ctx 91 (by decide) (by decide)]
      rfl
    | nonempty =>
      apply List.mem_of_getElem? (i := 92)
      rw [protocol_at ctx 92 (by decide) (by decide)]
      rfl
    | any =>
      apply List.mem_of_getElem? (i := 93)
      rw [protocol_at ctx 93 (by decide) (by decide)]
      rfl

/-- ENTER and VERIFY occupy the same component in the production export. Each physical row
consumes one complete HostCall. Both selections have the same 22-field witness layout. -/
theorem enter_verify_slot (ctx : Context) :
    (assembly ctx).tables[65]? = some (HostCallReceivers.profileNoop (p := SP1Prime) true).component ∧
      (HostCallReceivers.profileNoop (p := SP1Prime) true).component.circuit.name = "sp1.native.enter_or_verify" ∧
      (HostCallReceivers.profileNoop (p := SP1Prime) true).component.width = 22 ∧
      ((HostCallReceivers.profileNoop (p := SP1Prime) true).component.operations.interactions.map
        (·.channel.name)) = [(HostCallChip.channel (p := SP1Prime)).toRaw.name] := by
  rw [protocol_at ctx 65 (by decide) (by decide)]
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [Component.interactions_eq]
  change (((HostNoopChip.choiceMain (varFromOffset HostNoopChip.Inputs (F := Fp) 0)).operations
    (size HostNoopChip.Inputs)).interactions.map (·.channel.name)) = _
  simp [HostNoopChip.choiceMain, FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.circuit,
    Gadgets.Equality.main, circuit_norm, HostCallChip.channel]

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

private theorem core_at_bumps (ctx : Context) (i : ℕ) (lo : 55 ≤ i) (hi : i ≤ 56) :
    (assembly ctx).tables[i]? = (ProtectedLocalCore.tables (p := SP1Prime) ctx.image ctx.source)[i]? := by
  rw [observed, List.getElem?_append_left (by rw [List.length_mapIdx, original_length]; omega),
    List.getElem?_mapIdx]
  have untouched : HostOrdinaryReceipts.replace (p := SP1Prime) i = id := by
    funext table
    simp [HostOrdinaryReceipts.replace, show ¬ (7 ≤ i ∧ i < 32) by omega]
  rw [untouched, Option.map_id_fun]
  simp only [originalTables, HostFinalMemory.Installed, HostFinalMemory.tables_eq,
    List.getElem?_set_ne (show 4 ≠ i by omega), List.getElem?_set_ne (show 3 ≠ i by omega),
    List.getElem?_set_ne (show 57 ≠ i by omega)]
  rw [List.getElem?_append_left (by rw [HostFinalMemory.prefix_length]; change i < 66 + 20 + 8; omega),
    HostFinalMemory.beforeChecks, HostLocalCore.tables,
    List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; omega),
    List.getElem?_set_ne (show 58 ≠ i by omega)]
  rfl

/-- Both timestamp and CPU-state refresh providers are registered in the final physical inventory. -/
theorem bump_registered (ctx : Context) :
    providerTableFor .memoryBump ∈ (assembly ctx).tables ∧ providerTableFor .stateBump ∈ (assembly ctx).tables := by
  constructor
  · apply List.mem_of_getElem? (i := 55)
    rw [core_at_bumps ctx 55 (by decide) (by decide)]
    rfl
  · apply List.mem_of_getElem? (i := 56)
    rw [core_at_bumps ctx 56 (by decide) (by decide)]
    rfl

end SP1Clean.Export.InstalledAssembly
