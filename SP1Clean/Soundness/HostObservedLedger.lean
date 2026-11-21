import SP1Clean.Soundness.HostObserved
import SP1Clean.Soundness.OrdinaryObservation

/-! # Physical participants of the installed ordinary observation protocols

The receipt channel connects the 25 protected producers to the ordinary consumer. The observation
state channel connects that consumer, its three terminal components and the verifier endpoints.
-/

namespace SP1Clean.Soundness.HostObserved

open Circuit Air.Flat Channels Semantics
open SP1Clean.OrdinaryObservation (startFor finalFor)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

/-- Receipt publication retains the positions of all existing tables. -/
private theorem observed_tables :
    (ensemble image source target final).tables =
      (HostFinalMemory.Installed image source target final).tables.mapIdx HostOrdinaryReceipts.replace := by
  simp only [ensemble, ClosedVerifier.withInteractions, producers, HostOrdinaryReceipts.ensemble,
    HostSailBoundary.ensemble, PublicVerifier.install, HostFinalMemory.Installed]

/-- The observed physical inventory has 98 components before the immutable commitment provider. -/
theorem tables_length : (ensemble image source target final).tables.length = 98 := by
  rw [observed_tables, List.length_mapIdx]
  simp only [HostFinalMemory.Installed, HostFinalMemory.tables_eq, List.length_set, List.length_append,
    HostFinalMemory.prefix_length, HostCallReceivers.available, HostCallReceivers.availableFor,
    HostHintReadLocal.sourceResources, HostHintReadLocal.bankResources, OrdinaryObservation.tables,
    FinalMemoryChecks.checkTables, List.length_ofFn, List.length_cons, List.length_nil]

omit [Fact (2 ^ 25 < p)] in
private def mapReceiptSlot {tables : List (Component (ZMod p))} {component : Component (ZMod p)}
    (slot : TableSlot tables component) (outside : ¬ (7 ≤ slot.index.val ∧ slot.index.val < 32)) :
    TableSlot (tables.mapIdx HostOrdinaryReceipts.replace) component where
  index := ⟨slot.index.val, by simpa only [List.length_mapIdx] using slot.index.isLt⟩
  component_eq := by
    simp only [List.getElem_mapIdx, HostOrdinaryReceipts.replace, outside, dite_false, slot.component_eq]

/-- Publishing ordinary receipts retains each physical slot outside the 25 instruction producers. -/
def retainedSlot {component : Component (ZMod p)}
    (slot : TableSlot (HostFinalMemory.Installed image source target final).tables component)
    (outside : ¬ (7 ≤ slot.index.val ∧ slot.index.val < 32)) :
    TableSlot (ensemble image source target final).tables component :=
  (mapReceiptSlot slot outside).cast observed_tables.symm

private def observationPosition (i : Fin 4) :=
  (((((TableSlot.ofIndex (OrdinaryObservation.tables (p := p)) ⟨i.val, i.isLt⟩).appendRight
    (HostHintReadLocal.bankResources source.host.io.hints)).appendRight
    HostHintReadHandoff.wordResources).appendRight
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component))).appendRight
    ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer)).appendLeft
    (FinalMemoryChecks.checkTables target.sail.memorySnapshot)

private theorem position_val (i : Fin 4) :
    (observationPosition (p := p) (source := source) (image := image) (target := target) i).index.val = 90 + i.val := by
  simp only [observationPosition, TableSlot.appendRight, TableSlot.appendLeft, TableSlot.ofIndex,
    List.length_set, ProtectedLocalCore.tables_length, List.length_cons, List.length_nil,
    HostHintReadLocal.bankResources, HostHintReadHandoff.wordResources, HostCallReceivers.available, HostCallReceivers.availableFor,
    List.length_map, List.length_append, List.length_ofFn]
  omega

private def wrappedSlot {components : List (Component (ZMod p))} {component : Component (ZMod p)}
    (base : TableSlot components component) (outside : 90 ≤ base.index.val)
    (halt registers ram : Component (ZMod p)) (observed : List (Component (ZMod p)))
    (layout : (((components.set 57 halt).set 3 registers).set 4 ram).mapIdx HostOrdinaryReceipts.replace = observed) :
    TableSlot observed component :=
  (mapReceiptSlot (((base.setOther 57 halt (by omega)).setOther 3 registers
    (by change 3 ≠ base.index.val; omega)).setOther 4 ram (by change 4 ≠ base.index.val; omega))
    (by change ¬ (7 ≤ base.index.val ∧ base.index.val < 32); omega)).cast layout

/-- Positional identity of the consumer and each of the three verifier-selected terminals. -/
def observationSlot (i : Fin 4) : TableSlot (ensemble image source target final).tables
    ((OrdinaryObservation.tables (p := p))[i.val]'i.isLt) := by
  let base := observationPosition (p := p) (source := source) (image := image) (target := target) i
  have whereAt : base.index.val = 90 + i.val := position_val i
  apply wrappedSlot base (by omega)
  rw [observed_tables]
  apply congrArg (List.mapIdx HostOrdinaryReceipts.replace)
  exact HostFinalMemory.tables_eq.symm

private def observationChannels : List (RawChannel (ZMod p)) :=
  [InstructionReceipt.channel.toRaw, SP1Clean.OrdinaryObservation.stateChannel.toRaw]

private def silentComponent (component : Component (ZMod p)) : Bool :=
  (observationChannels (p := p)).all fun channel =>
    !(component.circuit.channels.map RawChannel.name).contains channel.name

omit [Fact (2 ^ 25 < p)] in
private theorem quiet_of_silent {component : Component (ZMod p)} (quiet : silentComponent component = true)
    {channel : RawChannel (ZMod p)} (listed : channel ∈ observationChannels (p := p)) :
    channel ∉ component.circuit.channels := by
  intro used
  have quietName := List.all_eq_true.mp quiet channel listed
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  rw [present] at quietName
  contradiction

private theorem original_participant {component : Component (ZMod p)}
    (member : component ∈ (HostFinalMemory.Installed image source target final).tables) {channel : RawChannel (ZMod p)}
    (listed : channel ∈ observationChannels (p := p)) (used : channel ∈ component.circuit.channels) :
    component ∈ OrdinaryObservation.tables := by
  have excluded {c : Component (ZMod p)} (quiet : silentComponent c = true) :
      channel ∈ c.circuit.channels → False := quiet_of_silent quiet listed
  simp only [HostFinalMemory.Installed, HostFinalMemory.tables_eq] at member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact (excluded rfl used).elim
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact (excluded rfl used).elim
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  swap
  · exact (excluded rfl used).elim
  rcases List.mem_append.mp member with base | checks
  swap
  · have quiet : (FinalMemoryChecks.checkTables (p := p) target.sail.memorySnapshot).all silentComponent = true := rfl
    exact (excluded (List.all_eq_true.mp quiet _ checks) used).elim
  simp only [HostFinalMemory.beforeChecks, HostLocalCore.tables, List.mem_append, HostHintReadLocal.sourceResources] at base
  rcases base with core | receivers | words | banks | observed
  · rcases List.mem_or_eq_of_mem_set core with core | rfl
    swap
    · exact (excluded rfl used).elim
    have registered := ProtectedLocalCore.component_channels_subset image source component core used
    have original : channel ∈ (LocalCore.baseEnsemble (p := p) image source).channels := by
      simp only [List.mem_cons] at registered
      rcases registered with rfl | rfl | original
      · simp [observationChannels, InstructionReceipt.channel, SP1Clean.OrdinaryObservation.stateChannel,
          WritePermissionProvider.channel, Channel.toRaw] at listed
      · simp [observationChannels, InstructionReceipt.channel, SP1Clean.OrdinaryObservation.stateChannel,
          ProgramImage.writePermissionTable, StaticTable.channel, StaticTable.ofRows, Channel.toRaw] at listed
      · exact original
    exact (HostFinalMemory.external_not_local (show channel ∈ HostFinalMemory.externalChannels from
      List.mem_cons_of_mem _ listed) original).elim
  · have quiet : ((HostHintReadHandoff.receiver :: HostCallReceivers.available (p := p)).map (·.component)).all silentComponent = true := rfl
    exact (excluded (List.all_eq_true.mp quiet _ receivers) used).elim
  · have quiet : (HostHintReadHandoff.wordResources (p := p)).all silentComponent = true := rfl
    exact (excluded (List.all_eq_true.mp quiet _ words) used).elim
  · have quiet : (HostHintReadLocal.bankResources (p := p) source.host.io.hints).all silentComponent = true := rfl
    exact (excluded (List.all_eq_true.mp quiet _ banks) used).elim
  · exact observed

/-- The observation table block occupies the four physical positions directly before final-memory checks. -/
theorem observationSlot_position (i : Fin 4) :
    (observationSlot (image := image) (source := source) (target := target) (final := final) i).index.val = 90 + i.val := by
  simp only [observationSlot, wrappedSlot, TableSlot.cast_index, mapReceiptSlot, TableSlot.setOther, position_val]

omit [Fact (2 ^ 25 < p)] in
private theorem indexOfSlot {rows : List (Component (ZMod p))}
    (unique : (rows.map (·.circuit.name)).Nodup)
    (choices : List (Component (ZMod p))) (location : (k : Fin choices.length) → TableSlot rows (choices.get k))
    (position : ∀ k, (location k).index.val = 90 + k.val) (count : choices.length = 4)
    (i : Fin rows.length) (belongs : ∃ component ∈ choices, (rows.get i).circuit.name = component.circuit.name) :
    90 ≤ i.val ∧ i.val < 94 := by
  obtain ⟨component, member, name⟩ := belongs
  obtain ⟨j, bound, atJ⟩ := List.mem_iff_getElem.mp member
  let slot := location ⟨j, bound⟩
  have eq : i.val = slot.index.val := by
    apply unique.eq_of_getElem_eq (by simpa only [List.length_map] using i.isLt)
      (by simpa only [List.length_map] using slot.index.isLt)
    rw [List.getElem_map, List.getElem_map, slot.component_eq]
    exact name.trans (congrArg (fun c : Component (ZMod p) => c.circuit.name) atJ.symm)
  have loc : slot.index.val = 90 + j := position ⟨j, bound⟩
  omega

omit [Fact (2 ^ 25 < p)] in
private theorem mapped_slot {old new : List (Component (ZMod p))}
    (replace : ℕ → Component (ZMod p) → Component (ZMod p))
    (mapped : new = old.mapIdx replace) (names : new.map (·.circuit.name) = old.map (·.circuit.name))
    (n : ℕ) (bound : n < new.length) :
    ∃ h : n < old.length, (new[n]'bound) = replace n (old[n]'h) ∧
      (new[n]'bound).circuit.name = (old[n]'h).circuit.name := by
  have h : n < old.length := by simpa only [mapped, List.length_mapIdx] using bound
  refine ⟨h, ?_, ?_⟩
  · simp only [mapped, List.getElem_mapIdx]
  · have eq := congrArg (fun values : List String => values[n]?) names
    simpa only [List.getElem?_map, List.getElem?_eq_getElem bound, List.getElem?_eq_getElem h, Option.map_some,
      Option.some.injEq] using eq

private theorem replaced_channels_at {n : ℕ} (bound : n < (HostFinalMemory.Installed image source target final).tables.length) :
    let old := ((HostFinalMemory.Installed image source target final).tables[n]'bound)
    (HostOrdinaryReceipts.replace n old).circuit.channels =
      old.circuit.channels ++ (if 7 ≤ n ∧ n < 32 then [InstructionReceipt.channel.toRaw] else []) := by
  let sail := HostSailBoundary.ensemble image source target final HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) (HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (HostFinalMemory.source_unique_names image source target.sail.memorySnapshot)
  have same : sail.tables = (HostFinalMemory.Installed image source target final).tables := by
    simp only [sail, HostSailBoundary.ensemble, PublicVerifier.install, HostFinalMemory.Installed]
  have within : n < sail.tables.length := by rwa [same]
  have metadata := HostOrdinaryReceipts.replacement_channels (image := image) (source := source) (target := target)
    (final := final) (others := HostCallReceivers.available) (resources := HostHintReadLocal.sourceResources source.host.io.hints)
    (channels := HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (names := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) ⟨n, within⟩
  change (HostOrdinaryReceipts.replace n (sail.tables[n]'within)).circuit.channels =
    (sail.tables[n]'within).circuit.channels ++ _ at metadata
  have item := List.getElem_of_eq same within
  rw [item] at metadata
  exact metadata

attribute [local irreducible] ensemble HostFinalMemory.ensemble observationSlot in
private theorem observation_index (n : ℕ) (h : n < (ensemble image source target final).tables.length)
    (names : ∃ component ∈ OrdinaryObservation.tables (p := p),
      ((ensemble image source target final).tables[n]'h).circuit.name = component.circuit.name) :
    90 ≤ n ∧ n < 94 := by
  let choices := OrdinaryObservation.tables (p := p)
  let slots (k : Fin choices.length) : TableSlot (ensemble image source target final).tables (choices.get k) :=
    observationSlot (image := image) (source := source) (target := target) (final := final) ⟨k.val, k.isLt⟩
  have located (k : Fin choices.length) : (slots k).index.val = 90 + k.val :=
    observationSlot_position (image := image) (source := source) (target := target) (final := final) ⟨k.val, k.isLt⟩
  exact indexOfSlot (ensemble image source target final).unique_names choices slots located rfl ⟨n, h⟩ names

attribute [local irreducible] ensemble HostFinalMemory.ensemble observationSlot in
private theorem physical_silent (witness : EnsembleWitness (ensemble image source target final))
    (i : Fin witness.tables.length) (channel : RawChannel (ZMod p)) (listed : channel ∈ observationChannels)
    (nonInstruction : channel ≠ InstructionReceipt.channel.toRaw ∨ ¬ (7 ≤ i.val ∧ i.val < 32))
    (outside : ¬ (90 ≤ i.val ∧ i.val < 94)) :
    (witness.tables.get i).interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro used
  let asm := ensemble image source target final
  let old := HostFinalMemory.Installed image source target final
  have bound : i.val < asm.tables.length := by rw [witness.same_length]; exact i.isLt
  have component := witness.same_circuits i.val bound
  change channel ∈ (witness.tables[i.val]'i.isLt).component.circuit.channels at used
  rw [← component] at used
  obtain ⟨originalBound, chosen, name⟩ := mapped_slot HostOrdinaryReceipts.replace
    (observed_tables (image := image) (source := source) (target := target) (final := final))
    table_names i.val bound
  rw [chosen, replaced_channels_at (image := image) (source := source) (target := target) (final := final) originalBound] at used
  rcases List.mem_append.mp used with priv | added
  · apply outside
    apply observation_index (image := image) (source := source) (target := target) (final := final) i.val bound
    exact ⟨old.tables[i.val]'originalBound,
      original_participant (image := image) (source := source) (target := target) (final := final) (List.getElem_mem originalBound) listed priv, name⟩
  · split at added
    · exact (nonInstruction.elim (fun neq => neq (List.mem_singleton.mp added)) (fun neg => neg ‹_ ∧ _›)).elim
    · contradiction

private theorem interval_silent (witness : EnsembleWitness (ensemble image source target final))
    (channel : RawChannel (ZMod p)) (listed : channel ∈ observationChannels) (first count : ℕ)
    (nonInstruction : channel ≠ InstructionReceipt.channel.toRaw ∨ first + count ≤ 7 ∨ 32 ≤ first)
    (outside : first + count ≤ 90 ∨ 94 ≤ first) :
    ((witness.tables.drop first).take count).flatMap (·.interactionsWith channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  obtain ⟨i, bound, eq⟩ := List.mem_iff_getElem.mp member
  have bounds : i < count ∧ first + i < witness.tables.length := by
    simp only [List.length_take, List.length_drop, lt_min_iff] at bound
    omega
  rw [← eq, List.getElem_take, List.getElem_drop]
  exact physical_silent witness ⟨first + i, bounds.2⟩ channel listed
    (by change channel ≠ _ ∨ ¬ (7 ≤ first + i ∧ first + i < 32); rcases nonInstruction with other | past | before; exact Or.inl other; all_goals right; omega)
    (by change ¬ (90 ≤ first + i ∧ first + i < 94); omega)

private theorem length_witness (witness : EnsembleWitness (ensemble image source target final)) :
    witness.tables.length = 98 := witness.same_length.symm.trans tables_length

/-- The complete receipt ledger splits into all 25 instruction tables and the observation block.
Repeated entries, padding and signed multiplicities are retained in the two segments. -/
theorem receipt_interactions (witness : EnsembleWitness (ensemble image source target final)) :
    witness.interactionsWith InstructionReceipt.channel.toRaw =
      ((witness.tables.drop 7).take 25).flatMap (·.interactionsWith InstructionReceipt.channel.toRaw) ++
      ((witness.tables.drop 90).take 4).flatMap (·.interactionsWith InstructionReceipt.channel.toRaw) := by
  let channel := (InstructionReceipt.channel (p := p)).toRaw
  change witness.interactionsWith channel = _
  have listed : channel ∈ observationChannels (p := p) := List.mem_cons_self
  have external : channel ∈ HostFinalMemory.externalChannels (p := p) := List.mem_cons_of_mem _ listed
  have before := interval_silent witness channel listed 0 7 (Or.inr (Or.inl (by decide))) (by decide)
  have middle := interval_silent witness channel listed 32 58 (Or.inr (Or.inr (by decide))) (by decide)
  have after := interval_silent witness channel listed 94 4 (Or.inr (Or.inr (by decide))) (by decide)
  have stop : witness.tables.drop 98 = [] := List.drop_eq_nil_iff.mpr (by rw [length_witness])
  have split := NativeCore.flatMap_split witness.tables (·.interactionsWith channel) 0 7
  simp only [List.drop_zero, Nat.zero_add] at split before
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.toTables, Tables.interactionsWith, verifier_external _ _ external]
  rw [ite_eq_right (by simp [channel, InstructionReceipt.channel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]), List.nil_append, split, before, List.nil_append,
    NativeCore.flatMap_split witness.tables _ 7 25, NativeCore.flatMap_split witness.tables _ 32 58, middle,
    List.nil_append, NativeCore.flatMap_split witness.tables _ 90 4, NativeCore.flatMap_split witness.tables _ 94 4,
    after, stop]
  simp [channel]

/-- The executable observation-state ledger consists of the verifier's actual source and target
endpoints followed by exactly the four guarded observation and terminal tables. -/
theorem state_interactions (witness : EnsembleWitness (ensemble image source target final)) :
    witness.interactionsWith SP1Clean.OrdinaryObservation.stateChannel.toRaw =
      [SP1Clean.OrdinaryObservation.stateChannel.pushedValue (startFor source.sail),
       SP1Clean.OrdinaryObservation.stateChannel.pulledValue (finalFor source.sail target.sail)] ++
      ((witness.tables.drop 90).take 4).flatMap (·.interactionsWith SP1Clean.OrdinaryObservation.stateChannel.toRaw) := by
  let channel := (SP1Clean.OrdinaryObservation.stateChannel (p := p)).toRaw
  change witness.interactionsWith channel = _
  have listed : channel ∈ observationChannels (p := p) := List.mem_cons_of_mem _ List.mem_cons_self
  have external : channel ∈ HostFinalMemory.externalChannels (p := p) := List.mem_cons_of_mem _ listed
  have other : channel ≠ InstructionReceipt.channel.toRaw := by simp [channel, InstructionReceipt.channel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]
  have before := interval_silent witness channel listed 0 90 (Or.inl other) (by decide)
  have after := interval_silent witness channel listed 94 4 (Or.inl other) (by decide)
  have stop : witness.tables.drop 98 = [] := List.drop_eq_nil_iff.mpr (by rw [length_witness])
  have split := NativeCore.flatMap_split witness.tables (·.interactionsWith channel) 0 90
  simp only [List.drop_zero, Nat.zero_add] at split before
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    EnsembleWitness.toTables, Tables.interactionsWith, verifier_external _ _ external]
  rw [split, before, List.nil_append,
    NativeCore.flatMap_split witness.tables _ 90 4, NativeCore.flatMap_split witness.tables _ 94 4, after, stop]
  simp [channel]

/-- The ordinary consumer or a particular terminal, read directly from the raw accepted table. -/
def observationTable (witness : EnsembleWitness (ensemble image source target final)) (i : Fin 4) :
    Table (ZMod p) :=
  (observationSlot i).table witness

private theorem fourRows {α : Type*} (rows : List α) (len : rows.length = 98)
    (slots : Fin 4 → α) (atSlot : ∀ i, slots i = rows[90 + i.val]'(by rw [len]; omega)) :
    (rows.drop 90).take 4 = [slots 0, slots 1, slots 2, slots 3] := by
  have array : (rows.drop 90).take 4 = List.ofFn slots := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, len, List.length_ofFn]
      decide
    · intro n left right
      have bound : n < 4 := by simpa only [List.length_ofFn] using right
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      exact (atSlot ⟨n, bound⟩).symm
  exact array.trans rfl

attribute [local irreducible] observationSlot ensemble in
private theorem observation_block (witness : EnsembleWitness (ensemble image source target final)) :
    (witness.tables.drop 90).take 4 =
      [observationTable witness 0, observationTable witness 1, observationTable witness 2, observationTable witness 3] := by
  apply fourRows witness.tables (length_witness witness) (observationTable witness)
  intro i
  unfold observationTable TableSlot.table
  exact getElem_congr_idx (c := witness.tables)
    (observationSlot_position (image := image) (source := source) (target := target) (final := final) i)

private theorem terminal_silent (table : Table (ZMod p)) (mode : SP1Clean.OrdinaryObservation.Mode)
    (registered : table.component = OrdinaryObservation.terminalComponent mode) :
    table.interactionsWith InstructionReceipt.channel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [registered, OrdinaryObservation.terminal_channels]
  simp [InstructionReceipt.channel, SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]

/-- On the accepted witness, all ordinary instruction pushes are matched against precisely the
signed pulls of the physical ordinary consumer. Its padding rows have zero multiplicity. -/
theorem receipt_rows (witness : EnsembleWitness (ensemble image source target final)) :
    witness.interactionsWith InstructionReceipt.channel.toRaw =
      ((witness.tables.drop 7).take 25).flatMap (·.interactionsWith InstructionReceipt.channel.toRaw) ++
      (OrdinaryObservation.rows (observationTable witness 0) witness.data).map
        (fun row => InstructionReceipt.channel.pulledIfValue row.2 row.1.receipt) := by
  rw [receipt_interactions, observation_block]
  simp only [List.flatMap_cons, List.flatMap_nil,
    terminal_silent (observationTable witness 1) .empty ((observationSlot 1).table_component witness),
    terminal_silent (observationTable witness 2) .nonempty ((observationSlot 2).table_component witness),
    terminal_silent (observationTable witness 3) .any ((observationSlot 3).table_component witness),
    List.append_nil, OrdinaryObservation.receipt_ledger (observationTable witness 0) witness.data
      ((observationSlot 0).table_component witness)]

open SP1Clean.OrdinaryObservation (TerminalInputs Mode terminal stateChannel)

open SP1Clean.Soundness.OrdinaryObservation (terminalRows terminalEdge terminal_state_ledger terminal_rows_valid)

/-- Every terminal in the three physical tables, tagged with the mode of its actual component. -/
def terminals (witness : EnsembleWitness (ensemble image source target final)) :
    List (Mode × TerminalInputs (ZMod p)) :=
  ((terminalRows (observationTable witness 1)).map (Prod.mk .empty)) ++
  ((terminalRows (observationTable witness 2)).map (Prod.mk .nonempty)) ++
  ((terminalRows (observationTable witness 3)).map (Prod.mk .any))

/-- A single chronological-edge ledger accounts for all live or padded observation rows and every
concrete terminal, with the verifier endpoints belonging to the supplied snapshots. -/
theorem state_rows (witness : EnsembleWitness (ensemble image source target final)) :
    witness.interactionsWith SP1Clean.OrdinaryObservation.stateChannel.toRaw =
      [SP1Clean.OrdinaryObservation.stateChannel.pushedValue (startFor source.sail),
       SP1Clean.OrdinaryObservation.stateChannel.pulledValue (finalFor source.sail target.sail)] ++
      (OrdinaryObservation.rows (observationTable witness 0) witness.data).flatMap
        (fun row => [SP1Clean.OrdinaryObservation.stateChannel.pulledIfValue row.2 row.1.previous,
          SP1Clean.OrdinaryObservation.stateChannel.pushedIfValue row.2 row.1.next]) ++
      (terminals witness).flatMap (fun tagged =>
        [SP1Clean.OrdinaryObservation.stateChannel.pulledValue (terminalEdge tagged.1 tagged.2).1,
         SP1Clean.OrdinaryObservation.stateChannel.pushedValue (terminalEdge tagged.1 tagged.2).2]) := by
  rw [state_interactions, observation_block]
  simp only [List.flatMap_cons, List.flatMap_nil, OrdinaryObservation.state_ledger (observationTable witness 0)
      witness.data ((observationSlot 0).table_component witness),
    terminal_state_ledger (observationTable witness 1) .empty ((observationSlot 1).table_component witness),
    terminal_state_ledger (observationTable witness 2) .nonempty ((observationSlot 2).table_component witness),
    terminal_state_ledger (observationTable witness 3) .any ((observationSlot 3).table_component witness),
    terminals, List.flatMap_append, List.flatMap_map, List.append_nil, List.append_assoc]

private theorem terminal_spec_of_constraints (table : Table (ZMod p)) (mode : Mode)
    (registered : table.component = OrdinaryObservation.terminalComponent mode) (constraints : table.Constraints) :
    table.Spec := by
  apply (Table.weakSoundness (table := table) ?_ constraints ?_).1
  · intro row occurs
    rw [registered]
    cases mode <;> trivial
  · apply table.guarantees_iff_channelGuarantees.mpr
    intro channel _
    apply (table.channelGuarantees_iff_forall channel).mpr
    intro interaction member
    by_cases same : channel = SP1Clean.OrdinaryObservation.stateChannel.toRaw
    · have free (ch : RawChannel (ZMod p)) (eq : ch = SP1Clean.OrdinaryObservation.stateChannel.toRaw)
          (mult : ZMod p) (msg : Vector (ZMod p) ch.arity) (data : ProverData (ZMod p)) : ch.Guarantees mult msg data := by
        subst ch
        simp [SP1Clean.OrdinaryObservation.stateChannel, Channel.toRaw]
      exact fun _ => free _ ((table.channel_eq_of_mem_interactionsWith member).trans same) _ _ _
    · have silent : channel ∉ table.component.circuit.channels := by
        rw [registered, OrdinaryObservation.terminal_channels]
        simp [same]
      rw [Table.interactionsWith_nil_of_channel_not_mem silent] at member
      contradiction

/-- Accepted local assertions establish the mode and both carry bits on every physical terminal. -/
theorem terminals_valid (witness : EnsembleWitness (ensemble image source target final)) (checked : witness.Constraints) :
    ∀ tagged ∈ terminals witness, tagged.2.Valid tagged.1 := by
  intro tagged member
  simp only [terminals, List.mem_append, List.mem_map] at member
  rcases member with ((⟨row, occurs, rfl⟩ | ⟨row, occurs, rfl⟩) | ⟨row, occurs, rfl⟩)
  · exact terminal_rows_valid _ .empty ((observationSlot 1).table_component witness)
      (terminal_spec_of_constraints _ .empty ((observationSlot 1).table_component witness)
        ((observationSlot 1).table_constraints witness checked)) row occurs
  · exact terminal_rows_valid _ .nonempty ((observationSlot 2).table_component witness)
      (terminal_spec_of_constraints _ .nonempty ((observationSlot 2).table_component witness)
        ((observationSlot 2).table_constraints witness checked)) row occurs
  · exact terminal_rows_valid _ .any ((observationSlot 3).table_component witness)
      (terminal_spec_of_constraints _ .any ((observationSlot 3).table_component witness)
        ((observationSlot 3).table_constraints witness checked)) row occurs

end SP1Clean.Soundness.HostObserved
