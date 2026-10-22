import SP1Clean.Soundness.HostHintReadLocal
import SP1Clean.Soundness.HostLocalCorePermissions

/-! # Authenticated permissions for installed HINT_READ writes

The real word consumers emit exactly eight unit permission pulls. All other installed host
components must likewise be consumers or silent, so the retained fixed image provider is the
only source. Its raw constraints and the ensemble's own balance authenticate each physical
byte request. The handler span and authenticated successor path supply the lower native-window
bound independently of prior RAM values and timestamps.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Model.Core HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance permissionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Neither physical word variant can manufacture a positive permission. -/
theorem word_permission_pulls (last : Bool) : WritePermission.Pulls (HintReadCoverage.view (p := p) last).component := by
  intro data physical checked interaction member
  have binary := HintReadCoverage.row_activity_binary (last, Environment.fromArray physical data) checked
  rw [HintReadWriteLedger.row_permission_values (last, Environment.fromArray physical data)] at member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  rcases binary with inactive | active
  · exact Or.inl (by simp only [Channel.pulledIfValue, inactive, neg_zero])
  · exact Or.inr (congrArg Neg.neg active)

/-- The existing non-RAM handlers are all silent on byte permissions. -/
theorem available_permission_pulls : ∀ component ∈ (HostCallReceivers.available (p := p)).map (·.component),
    WritePermission.Pulls component := by
  have checked : ((HostCallReceivers.available (p := p)).map (·.component)).all (fun component =>
      !(component.circuit.channels.map RawChannel.name).contains
        (WritePermissionProvider.channel (p := p)).toRaw.name) = true := rfl
  intro component member
  apply WritePermission.pulls_of_silent
  intro used
  have valid := List.all_eq_true.mp checked component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at valid
  contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source ((receiver :: others).map (·.component) ++ (wordResources ++ resources))).map (·.circuit.name)).Nodup}

theorem auxiliary_permission_pulls
    (pulls : ∀ component ∈ others.map (·.component) ++ resources, WritePermission.Pulls component) :
    ∀ component ∈ (receiver :: others).map (·.component) ++ (wordResources ++ resources),
      WritePermission.Pulls component := by
  intro component member
  simp only [List.map_cons, List.mem_append, List.mem_cons, wordResources, receiver,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | other) | ((rfl | rfl) | extra)
  · apply WritePermission.pulls_of_silent
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at present
    contradiction
  · exact pulls component (List.mem_append_left _ other)
  · exact word_permission_pulls false
  · exact word_permission_pulls true
  · exact pulls component (List.mem_append_right _ extra)

/-- The installed handler and word rows consume their private protocols without providing
writable-interval membership. Remaining components expose the same static interface. -/
theorem auxiliary_membership_silent
    (members : ∀ component ∈ others.map (·.component) ++ resources,
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements) :
    ∀ component ∈ (receiver :: others).map (·.component) ++ (wordResources ++ resources),
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
  have checked : (receiver.component :: wordResources (p := p)).all (fun component =>
      !(component.circuit.channelsWithRequirements.map RawChannel.name).contains
        (image.writePermissionTable (p := p)).name) = true := by
    unfold ProgramImage.writePermissionTable
    rfl
  have fixed (component : Component (ZMod p))
      (member : component ∈ receiver.component :: wordResources (p := p)) :
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
    intro used
    have valid := List.all_eq_true.mp checked component member
    change (!(component.circuit.channelsWithRequirements.map RawChannel.name).contains
      image.writePermissionTable.channel.toRaw.name) = true at valid
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at valid
    contradiction
  intro component member
  simp only [List.map_cons, List.mem_append, List.mem_cons, wordResources, receiver,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | other) | ((rfl | rfl) | extra)
  · exact fixed _ (by simp [receiver])
  · exact members component (List.mem_append_left _ other)
  · exact fixed _ (by simp [wordResources])
  · exact fixed _ (by simp [wordResources])
  · exact members component (List.mem_append_right _ extra)

/-- Every actual word-byte pull is authenticated by the installed fixed image provider. -/
theorem word_permission_permitted (witness : EnsembleWitness (ensemble image source others resources channels names))
    (pulls : ∀ component ∈ others.map (·.component) ++ resources, WritePermission.Pulls component)
    (members : ∀ component ∈ others.map (·.component) ++ resources,
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    (membershipBalance : witness.BalancedChannel image.writePermissionTable.channel.toRaw)
    (address : fields 3 (ZMod p))
    (member : WritePermissionProvider.channel.pulledValue address ∈
      (wordTables witness).flatMap (·.interactionsWith WritePermissionProvider.channel.toRaw)) :
    WritePermissionProvider.Permitted image address := by
  apply HostLocalCore.permission_pull_permitted witness (auxiliary_permission_pulls pulls) (auxiliary_membership_silent members)
    constraints balanced membershipBalance address
  obtain ⟨table, tableMem, member⟩ := List.mem_flatMap.mp member
  exact EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, wordTables_mem witness table tableMem, member⟩)

private theorem row_address_lower (witness : EnsembleWitness (ensemble image source others resources channels names))
    (interface : ExtensionInterface others resources) (constraints : witness.Constraints)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (handlerSpecs : (handlerTable witness).Spec)
    (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (wordTables witness)) :
    2 ^ 16 ≤ Address.toNat (HintReadCoverage.rowInput row).address := by
  obtain ⟨env, handlerMem, clock⟩ := consumer_has_handler_of_balancedChannel witness interface cursor wordSpecs row member
  have selected := balanced_for_of_channels witness interface constraints ordering calls cursor env handlerMem
  rw [HostHintReadCoverage.handler_cursor] at selected
  have fixed := HintReadCoverage.selection_fixed (wordTables witness)
    (HostHintReadPartition.keepWord (HostHintReadPartition.callClock env)) (wordTables_aligned witness)
  have lower := HintReadCoverage.address_lower _ _ _
    (TransitionView.selectTables_aligned _ _ (fun last => (HintReadCoverage.view last).component)
      (HostHintReadPartition.keepWord (HostHintReadPartition.callClock env)) fixed (wordTables_aligned witness))
    (wordSpecs.select (HostHintReadPartition.keepWord (HostHintReadPartition.callClock env)) fixed) selected row (by
      rw [TransitionView.readIndexedActiveRows_selectTables]
      exact List.mem_filter.mpr ⟨member, by
        simp only [HostHintReadPartition.keepWord, HostHintReadPartition.keepState,
          HintReadCoverage.rowInput]
        exact decide_eq_true clock.symm⟩)
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp handlerMem
  have valid := handlerSpecs physical physicalMem
  have shared : (handlerTable witness).data = witness.data :=
    witness.same_data _ (handlerTable_mem witness)
  rw [Table.environment, shared, handlerTable_component] at valid
  have span : HintReadSpan.Spec (HostHintReadCoverage.input (Environment.fromArray physical witness.data)).span :=
    valid.2.2.2.2.2.2.2.2.1
  exact le_trans span.2.2.1.1 lower

private theorem permission_request_lower (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) (wordSpecs : HintReadCoverage.Steps tables)
    (lower : ∀ row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view tables,
      2 ^ 16 ≤ Address.toNat (HintReadCoverage.rowInput row).address)
    (address : fields 3 (ZMod p))
    (member : WritePermissionProvider.channel.pulledValue address ∈
      tables.flatMap (·.interactionsWith WritePermissionProvider.channel.toRaw))
    : 2 ^ 16 ≤ Address.toNat address := by
  rw [HintReadWriteLedger.permission_ledger _ aligned] at member
  obtain ⟨row, rowMem, present⟩ := List.mem_flatMap.mp member
  obtain ⟨index, equal⟩ := List.mem_ofFn.mp present
  have enabled : HintReadCoverage.rowActivity row = 1 := by
    have mult := congrArg Interaction.mult equal
    exact neg_inj.mp mult
  have activeMem := HintReadCoverage.mem_active_rows.mpr ⟨rowMem, enabled⟩
  have addressEq := congrArg (fromElements (M := fields 3)) (Vector.toArray_inj.mp (congrArg Interaction.msg equal))
  simp only [ProvableType.fromElements_toElements] at addressEq
  have valid := wordSpecs.step row activeMem
  have lower := lower row activeMem
  have offset : Address.toNat address = Address.toNat (HintReadCoverage.rowInput row).address + index.val := by
    rw [← addressEq]
    exact Address.toNat_offset (HintReadCoverage.rowInput row).address valid.2.2.1
      index.val (by have := index.isLt; omega)
  rw [offset]
  exact le_trans lower (Nat.le_add_right _ _)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem byte_permitted (readOnly : ℕ → Bool) (address : ℕ)
    (lower : 2 ^ 16 ≤ address) (upper : address < 2 ^ 48) (writable : readOnly address = false) :
    (HostMemoryPolicy.mk readOnly NativeLayout.guestMemory).permits address 1 = true := by
  apply (HostMemoryPolicy.permits_iff _ _ _).mpr
  refine ⟨lower, upper, ?_⟩
  intro byte bound
  have zero : byte = 0 := by omega
  simpa only [zero, Nat.add_zero] using writable

/-- Fixed-provider writability and the checked handler span yield the actual host policy. -/
theorem word_permission_policy (witness : EnsembleWitness (ensemble image source others resources channels names))
    (interface : ExtensionInterface others resources)
    (pulls : ∀ component ∈ others.map (·.component) ++ resources, WritePermission.Pulls component)
    (members : ∀ component ∈ others.map (·.component) ++ resources,
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements)
    (constraints : witness.Constraints) (permissions : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    (membershipBalance : witness.BalancedChannel image.writePermissionTable.channel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (handlerSpecs : (handlerTable witness).Spec)
    (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (address : fields 3 (ZMod p))
    (member : WritePermissionProvider.channel.pulledValue address ∈
      (wordTables witness).flatMap (·.interactionsWith WritePermissionProvider.channel.toRaw)) :
    (HostMemoryPolicy.mk image.readOnly NativeLayout.guestMemory).permits (Address.toNat address) 1 = true := by
  have permitted := word_permission_permitted witness pulls members constraints permissions membershipBalance address member
  exact byte_permitted image.readOnly (Address.toNat address)
    (permission_request_lower (wordTables witness) (wordTables_aligned witness) wordSpecs
      (row_address_lower witness interface constraints ordering calls cursor handlerSpecs wordSpecs) address member)
    permitted.2.1 permitted.2.2

/-- The installed AIR supplies all handoff/cursor accounting for concrete HINT_READ execution.
The fixed image provider authenticates every permission. The remaining premises are local
specifications, current queue and immutable record authentication, and current register observations. -/
theorem run_of_witness (witness : EnsembleWitness (ensemble image source others resources channels names))
    (interface : ExtensionInterface others resources)
    (pulls : ∀ component ∈ others.map (·.component) ++ resources, WritePermission.Pulls component)
    (members : ∀ component ∈ others.map (·.component) ++ resources,
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements)
    (constraints : witness.Constraints)
    (permissions : witness.BalancedChannel WritePermissionProvider.channel.toRaw)
    (membershipBalance : witness.BalancedChannel image.writePermissionTable.channel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (handlerSpecs : (handlerTable witness).Spec)
    (wordSpecs : HintReadCoverage.Steps (wordTables witness))
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (Environment.fromArray · witness.data))
    (host : HostState) (store : HintQueue.Store)
    (current : (HostHintReadCoverage.input env).previous.Binds store host.io.hints)
    (header : (HostHintReadCoverage.input env).node.Binds store)
    (ending : (HostHintReadCoverage.input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (wordTables witness),
      HostHintReadPartition.clock (HintReadCoverage.rowInput row).previous = HostHintReadPartition.callClock env →
        ((HintReadCoverage.rowInput row).step row.1).word.Binds store)
    (running : host.exitCode = none) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 (HostHintReadCoverage.input env).call.arg2)) :
    ∃ bytes rest, host.io.hints = bytes :: rest ∧ (HostHintReadCoverage.input env).next.Binds store rest ∧
      host.run ⟨{ readOnly := image.readOnly }, p⟩ context = some (HostHintReadChip.execution (HostHintReadCoverage.input env) host bytes rest) ∧
      ((TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) (wordTables witness) (wordTables_aligned witness))).map
        HintReadWrites.produced).Perm (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes) := by
  have shared : (handlerTable witness).data = witness.data :=
    witness.same_data _ (handlerTable_mem witness)
  have present : env ∈ (handlerTable witness).table.map (fun row => (handlerTable witness).environment row) := by
    simpa only [Table.environment, shared] using member
  have unique := handler_clocks_nodup_of_channels witness interface constraints ordering calls
  exact HostHintReadPartition.run_of_shared_tables (handlerTable witness) (handlerTable_component witness) handlerSpecs (wordTables witness) (wordTables_aligned witness) wordSpecs env present
    (by simpa only [Table.environment, shared] using unique)
    (cursor_balanced_of_balancedChannel witness interface cursor)
    host store current header ending words running ⟨{ readOnly := image.readOnly }, p⟩ context
    (word_permission_policy witness interface pulls members constraints permissions membershipBalance ordering calls cursor handlerSpecs wordSpecs) code arg1 arg2


end SP1Clean.Soundness.HostHintReadLocal
