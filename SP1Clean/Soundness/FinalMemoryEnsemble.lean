import SP1Clean.Soundness.OrderedMemoryEnsemble
import ToClean.Air.ChannelClosure
import ToClean.Air.EnsembleProjection
import ToClean.Air.ComponentOutput
import SP1Clean.Proofs.Chips.OrderedFinalProvider

/-! # Native final-memory inventory

Final register and RAM rows share a private control channel with fixed endpoints. Every active
provider row consumes one canonical Memory record; padding retains zero-multiplicity
occurrences. The shared inventory proof excludes repeated active locations across both tables. Connecting this
inventory to the timed machine establishes that these are the final values; that claim is not a local finalizer assumption.
-/

namespace SP1Clean.Soundness.FinalMemoryEnsemble

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {PublicIO : TypeMap} [ProvableType PublicIO]

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

open SP1Clean.OrderedFinalProvider

/-- Both finalizers append activity after the ordered Memory-record input. -/
def activity : Expression (ZMod p) :=
  .var ⟨size (OrderedMemoryProvider.Inputs MemoryMsg)⟩

def registerView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.FinalSpec
    FinalRegisterProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid) (by
      simp [GeneralFormalCircuit.channels, FinalRegisterProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel])

def ramView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.RamFinalSpec
    FinalRamProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid.1) (by
      simp [GeneralFormalCircuit.channels, FinalRamProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel, byteChannel])

/-- The guarded register input ends at the shared activity column. -/
theorem registerView_activity : (registerView (p := p)).activity = activity := by
  simp only [registerView, OrderedMemoryEnsemble.providerView, varFromOffset_pair,
    ProvableType.varFromOffset_field, Nat.zero_add, activity]

/-- The guarded RAM input has the same activity column as the register finalizer. -/
theorem ramView_activity : (ramView (p := p)).activity = activity := by
  simp only [ramView, OrderedMemoryEnsemble.providerView, varFromOffset_pair,
    ProvableType.varFromOffset_field, Nat.zero_add, activity]

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def viewFor : TableId → TransitionView (OrderedBoundary.channel (p := p) channelName)
  | .registers => registerView
  | .ram => ramView
  | .terminal => OrderedMemoryEnsemble.terminalView channelName (by decide)

/-- Final rows use only Byte, Memory, and their own private ordering channel. -/
theorem view_channels_subset (id : TableId) :
    (viewFor (p := p) id).component.circuit.channels ⊆
      [byteChannel.toRaw, memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] := by
  cases id
  · change [(memoryChannel (p := p)).toRaw, byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
      memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp
  · change [(byteChannel (p := p)).toRaw, memoryChannel.toRaw, byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw,
      memoryChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp
  · change [(byteChannel (p := p)).toRaw, (OrderedBoundary.channel channelName).toRaw,
      (OrderedBoundary.channel channelName).toRaw] ⊆ _
    simp

/-- Finalizers have no data-dependent legacy lookups; Byte checks use channels. -/
theorem view_lookups (id : TableId) :
    (viewFor (p := p) id).component.operations.lookups = [] := by
  cases id <;>
    simp [viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView,
      OrderedMemoryEnsemble.terminalView, Component.lookups_eq, Component.rowOperations,
      OrderedMemoryProvider.circuit, Guarded.circuit, OrderedMemoryProvider.activeCircuit, FinalRegisterProvider.circuit, FinalRamProvider.circuit,
      OrderedBoundaryEnd.circuit, circuit_norm]

/-- Proof view of the same address and order assertions, before Memory is authenticated. -/
private def addressView : TableId → TransitionView (OrderedBoundary.channel (p := p) channelName)
  | .registers => OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.FinalSpec
      FinalRegisterProvider.addressCircuit (fun _ _ _ valid => valid.1) (fun _ valid => valid) (by
        simp [GeneralFormalCircuit.channels, FinalRegisterProvider.addressCircuit, circuit_norm])
  | .ram => OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.RamFinalSpec
      FinalRamProvider.addressCircuit (fun _ _ _ valid => valid.1) (fun _ valid => valid.1) (by
        simp [GeneralFormalCircuit.channels, FinalRamProvider.addressCircuit, circuit_norm,
          OrderedBoundary.channel, channelName, byteChannel])
  | .terminal => OrderedMemoryEnsemble.terminalView channelName (by decide)

private theorem addressView_constraints (id : TableId) :
    (addressView (p := p) id).component.operations.constraints =
      (viewFor id).component.operations.constraints := by
  cases id <;>
    simp only [addressView, viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView,
      Component.constraints_eq, Component.rowOperations, OrderedMemoryProvider.circuit,
      Guarded.circuit, Guarded.main_constraints, OrderedMemoryProvider.activeCircuit,
      OrderedMemoryProvider.main, FinalRegisterProvider.circuit, FinalRamProvider.circuit,
      FinalRegisterProvider.main, FinalRamProvider.main, FinalRegisterProvider.addressCircuit,
      FinalRamProvider.addressCircuit, circuit_norm]

private theorem addressView_lookups (id : TableId) :
    (addressView (p := p) id).component.operations.lookups = [] := by
  cases id <;>
    simp [addressView, OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
      Component.lookups_eq, Component.rowOperations, OrderedMemoryProvider.circuit,
      Guarded.circuit, OrderedMemoryProvider.activeCircuit, FinalRegisterProvider.addressCircuit,
      FinalRamProvider.addressCircuit, OrderedBoundaryEnd.circuit, circuit_norm]

private theorem addressView_byte (id : TableId) :
    (addressView (p := p) id).component.operations.interactionsWith byteChannel.toRaw =
      (viewFor id).component.operations.interactionsWith byteChannel.toRaw := by
  cases id <;>
    simp only [addressView, viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView,
      Component.interactionsWith_eq, Component.rowOperations, OrderedMemoryProvider.circuit,
      Guarded.circuit, Guarded.main_interactionsWith, OrderedMemoryProvider.activeCircuit,
      OrderedMemoryProvider.main, FinalRegisterProvider.circuit, FinalRamProvider.circuit,
      FinalRegisterProvider.main, FinalRamProvider.main, FinalRegisterProvider.addressCircuit,
      FinalRamProvider.addressCircuit, GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm,
      List.filter_append, List.filter_cons, List.filter_nil, ChannelInteraction.toRaw,
      memoryChannel_eq_byteChannel_false, ↓reduceIte, List.append_nil]

/-- Finalizer semantics require only raw constraints and Byte guarantees, before Memory grounding. -/
theorem view_spec (id : TableId) (env : Environment (ZMod p))
    (constraints : (viewFor id).component.operations.ConstraintsHold env)
    (byte : (viewFor id).component.operations.ChannelGuarantees byteChannel.toRaw env) :
    (viewFor id).component.Spec env := by
  have constraints : (addressView id).component.operations.ConstraintsHold env := by
    simpa only [Operations.ConstraintsHold, addressView_constraints, addressView_lookups,
      view_lookups] using constraints
  have byte : (addressView id).component.operations.ChannelGuarantees byteChannel.toRaw env := by
    apply Operations.channelGuarantees_of_interactionsWith_subset _ _ _ ?_ env byte
    rw [addressView_byte]
  suffices (addressView id).component.Spec env by cases id <;> exact this
  have assumptions : (addressView (p := p) id).component.CircuitAssumptions env := by
    cases id
    · intro _
      trivial
    · intro _
      trivial
    · trivial
  have channels : (addressView (p := p) id).component.circuit.channelsWithGuarantees ⊆
      [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] := by
    cases id
    · change [(byteChannel (p := p)).toRaw, (OrderedBoundary.channel channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · change [(byteChannel (p := p)).toRaw, byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · exact List.Subset.refl _
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ ((addressView id).component.inChannelsOrGuarantees env)]
  intro channel member
  rcases List.mem_cons.mp (channels member) with rfl | member
  · exact byte
  · obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _

/-- Both ordered finalizers return their input record; decode that shared typed prefix. -/
def rowRecord (env : Environment (ZMod p)) : MemoryMsg (ZMod p) :=
  (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).1.payload

omit [Fact (2 ^ 17 < p)] in
private theorem eval_payload (env : Environment (ZMod p))
    (input : Var (OrderedMemoryProvider.RowInput MemoryMsg) (ZMod p)) :
    Eval.eval env input.1.payload = (Eval.eval env input).1.payload := by
  rcases input with ⟨⟨payload, link⟩, active⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem rowRecord_eval (env : Environment (ZMod p)) :
    Eval.eval env (varFromOffset (F := ZMod p) (OrderedMemoryProvider.RowInput MemoryMsg) 0).1.payload =
      rowRecord env := by
  rw [eval_payload, eval_varFromOffset_valueFromOffset]
  rfl

theorem registerView_output (env : Environment (ZMod p)) :
    (registerView (p := p)).component.rowOutput env = rowRecord env := rowRecord_eval env

theorem ramView_output (env : Environment (ZMod p)) :
    (ramView (p := p)).component.rowOutput env = rowRecord env := rowRecord_eval env

def recordFor (id : TableId) (env : Environment (ZMod p)) : Option (MemoryMsg (ZMod p)) :=
  match id with
  | .registers | .ram => some (rowRecord env)
  | .terminal => none

/-- Finalizer contracts read only committed cells. Dropping unrelated tables changes canonical
data, but does not change the meaning of these three components' decoded rows. -/
theorem view_spec_setData (id : TableId) (row : Array (ZMod p))
    (data data' : ProverData (ZMod p))
    (valid : (viewFor id).component.Spec (Environment.fromArray row data)) :
    (viewFor id).component.Spec (Environment.fromArray row data') := by
  have input : (viewFor id).component.rowInput (Environment.fromArray row data') =
      (viewFor id).component.rowInput (Environment.fromArray row data) :=
    ProvableType.valueFromOffset_congr _ 0 (fun _ _ => rfl)
  have output : (viewFor id).component.rowOutput (Environment.fromArray row data') =
      (viewFor id).component.rowOutput (Environment.fromArray row data) :=
    Component.rowOutput_congr _ rfl
  unfold Component.Spec at valid ⊢
  rw [input, output]
  cases id <;> exact valid

def inventory : OrderedMemoryEnsemble.Inventory channelName (MemoryBoundary.FinalSpec (p := p)) where
  Index := TableId
  tableIds := [.registers, .ram, .terminal]
  viewFor := viewFor
  recordFor := recordFor
  strict := by
    intro id env valid active
    cases id with
    | registers =>
      dsimp only [viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView] at active
      exact (valid.2 (OrderedMemoryEnsemble.active_input (Payload := MemoryMsg) active)).2.1.2.2
    | ram =>
      dsimp only [viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView] at active
      exact (valid.2 (OrderedMemoryEnsemble.active_input (Payload := MemoryMsg) active)).2.1.2.2
    | terminal => exact valid.2
  recordFor_spec := by
    intro id env valid active record found
    cases id with
    | registers =>
      obtain rfl := Option.some.inj found
      dsimp only [viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView] at active
      have child := valid.2 (OrderedMemoryEnsemble.active_input (Payload := MemoryMsg) active)
      have result := And.intro child.1 child.2.2
      simp only [viewFor, registerView_output] at result
      exact result
    | ram =>
      obtain rfl := Option.some.inj found
      dsimp only [viewFor, registerView, ramView, OrderedMemoryEnsemble.providerView] at active
      have child := valid.2 (OrderedMemoryEnsemble.active_input (Payload := MemoryMsg) active)
      have result := And.intro child.1.1 child.2.2
      simp only [viewFor, ramView_output] at result
      exact result
    | terminal => contradiction

/-- The two finalizers and their ordering terminal have distinct canonical names. -/
theorem inventory_unique_names :
    ((inventory (p := p)).views.map (·.component.circuit.name)).Nodup := by
  change [
    (registerView (p := p)).component.circuit.name, ramView.component.circuit.name,
    (OrderedMemoryEnsemble.terminalView channelName (by decide)).component.circuit.name].Nodup
  simp [registerView, ramView,
    OrderedMemoryEnsemble.providerView, OrderedMemoryEnsemble.terminalView,
    OrderedMemoryProvider.circuit, Guarded.circuit, OrderedMemoryProvider.activeCircuit, OrderedBoundaryEnd.circuit,
    FinalRegisterProvider.circuit, FinalRamProvider.circuit, channelName]
  decide

def ensemble {PublicIO : TypeMap} [ProvableType PublicIO] (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (names : (((inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup)
    (channelNames : (((OrderedBoundary.channel channelName).toRaw :: channels).map (·.name)).Nodup := by assumption)
    (registered : ∀ table ∈ (inventory (p := p)).views.map (·.component) ++ auxiliary,
      table.circuit.channels ⊆ (OrderedBoundary.channel channelName).toRaw :: channels := by assumption) :=
  inventory.ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered

variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
variable {names : (((inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}
variable {channelNames : (((OrderedBoundary.channel channelName).toRaw :: channels).map (·.name)).Nodup}
variable {registered : ∀ table ∈ (inventory (p := p)).views.map (·.component) ++ auxiliary,
      table.circuit.channels ⊆ (OrderedBoundary.channel channelName).toRaw :: channels}

/-- The original physical record occurrences, including inactive rows. -/
def physicalRecords (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered)) :=
  inventory.physicalRecords witness

def records (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered)) := inventory.records witness

/-- Both provider tables retain every physical record and its activity; the terminal adds none. -/
theorem physicalRecords_eq (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered)) :
    physicalRecords witness =
      (witness.tables[0]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.map
          (fun row => (Environment.fromArray row witness.data activity,
            rowRecord (Environment.fromArray row witness.data))) ++
      (witness.tables[1]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.map
          (fun row => (Environment.fromArray row witness.data activity,
            rowRecord (Environment.fromArray row witness.data))) := by
  have length : 3 ≤ witness.tables.length := by
    rw [← witness.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have front : witness.tables.take 3 = [witness.tables[0], witness.tables[1], witness.tables[2]] := by
    rw [List.take_succ_eq_append_getElem (by omega : 2 < witness.tables.length),
      List.take_succ_eq_append_getElem (by omega : 1 < witness.tables.length),
      List.take_succ_eq_append_getElem (by omega : 0 < witness.tables.length)]
    rfl
  change ((TransitionView.readIndexedRows [TableId.registers, .ram, .terminal]
    (witness.tables.take 3)).filterMap fun row =>
      (recordFor row.1 row.2).map fun record => (row.2 (viewFor row.1).activity, record)) = _
  rw [front]
  simp only [TransitionView.readIndexedRows, List.zip_cons_cons, List.zip_nil_right,
    List.flatMap_cons, List.flatMap_nil, List.filterMap_append, List.filterMap_map,
    Function.comp_def, recordFor, Option.map_some, Option.map_none,
    List.filterMap_eq_map', List.filterMap_none, List.append_nil, Table.environment,
    witness.same_data _ (List.getElem_mem _), viewFor, registerView_activity, ramView_activity]
  rfl

/-- The shared decoder reads the original output of each physical register and RAM row;
the ordering terminal contributes no Memory record. -/
theorem records_eq (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered)) :
    records witness =
      ((witness.tables[0]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.filter (fun row =>
          decide (Environment.fromArray row witness.data activity = 1))).map
          (fun row => rowRecord (Environment.fromArray row witness.data)) ++
      ((witness.tables[1]'(by rw [← witness.same_length]; simp [ensemble,
        OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
        OrderedMemoryEnsemble.Inventory.views, inventory])).table.filter (fun row =>
          decide (Environment.fromArray row witness.data activity = 1))).map
          (fun row => rowRecord (Environment.fromArray row witness.data)) := by
  rw [records, inventory.records_eq_active_physical witness]
  change ((physicalRecords witness).filter fun row => decide (row.1 = 1)).map Prod.snd = _
  rw [physicalRecords_eq]
  simp only [List.filter_append, List.filter_map, List.map_append, List.map_map, Function.comp_def]

theorem records_valid (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered))
    (valid : witness.Spec) : ∀ record ∈ records witness, MemoryBoundary.FinalSpec record :=
  inventory.records_valid witness valid

theorem records_locations_nodup (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((records witness).map MemoryMsg.locOf).Nodup :=
  inventory.records_locations_nodup witness privateChannel valid balanced

/-- The finite record decoder agrees exactly with each table's physical Memory interactions. -/
theorem recordFor_interactions (id : TableId) (env : Environment (ZMod p)) :
    (viewFor id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((recordFor id env).toList).map
        (memoryChannel.pulledIfValue (env (viewFor id).activity)) := by
  cases id with
  | registers =>
    simp only [viewFor, registerView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit, Guarded.circuit]
    rw [Guarded.main_interactionsWith]
    simp only [OrderedMemoryProvider.activeCircuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRegisterProvider.circuit]
    rw [FinalRegisterProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, AbstractInteraction.eval_guard, Channel.eval_pulled,
      Channel.pulledValue, mul_one, recordFor, Option.toList_some,
      eval_payload, eval_varFromOffset_valueFromOffset]
    rfl
  | ram =>
    simp only [viewFor, ramView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit, Guarded.circuit]
    rw [Guarded.main_interactionsWith]
    simp only [OrderedMemoryProvider.activeCircuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRamProvider.circuit]
    rw [FinalRamProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, AbstractInteraction.eval_guard, Channel.eval_pulled,
      Channel.pulledValue, mul_one, recordFor, Option.toList_some,
      eval_payload, eval_varFromOffset_valueFromOffset]
    rfl
  | terminal =>
    exact OrderedMemoryEnsemble.terminalView_memory_interactions _ (by decide) env

/-- The physical boundary ledger retains every record and its actual pull activity. -/
theorem memory_interactions_eq (witness : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered)) :
    (witness.tables.take (inventory (p := p)).views.length).flatMap (·.interactionsWith memoryChannel.toRaw) =
      (physicalRecords witness).map (fun row => memoryChannel.pulledIfValue row.1 row.2) := by
  exact inventory.memory_interactions_eq witness memoryChannel.pulledIfValue
    recordFor_interactions

/-- The decoder depends only on the two finalizer row arrays.
Different physical proof views may retain different suffixes or verifier interfaces. -/
theorem records_congr_rows {OtherPublicIO : TypeMap} [ProvableType OtherPublicIO]
    {otherAuxiliary : List (Component (ZMod p))}
    {otherChannels : List (RawChannel (ZMod p))}
    {otherNames : (((inventory (p := p)).views.map (·.component) ++ otherAuxiliary).map (·.circuit.name)).Nodup}
    (first : EnsembleWitness (ensemble (PublicIO := PublicIO) auxiliary channels names channelNames registered))
    {otherChannelNames : (((OrderedBoundary.channel channelName).toRaw :: otherChannels).map (·.name)).Nodup}
    {otherRegistered : ∀ table ∈ (inventory (p := p)).views.map (·.component) ++ otherAuxiliary,
      table.circuit.channels ⊆ (OrderedBoundary.channel channelName).toRaw :: otherChannels}
    (second : EnsembleWitness (ensemble (PublicIO := OtherPublicIO) otherAuxiliary otherChannels otherNames otherChannelNames otherRegistered))
    (rows : (first.tables.take 2).map (·.table) = (second.tables.take 2).map (·.table)) :
    records first = records second := by
  have firstBound : 2 ≤ first.tables.length := by
    rw [← first.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have secondBound : 2 ≤ second.tables.length := by
    rw [← second.same_length]
    simp [ensemble, OrderedMemoryEnsemble.Inventory.ensemble, OrderedBoundaryEnsemble.ensemble,
      OrderedMemoryEnsemble.Inventory.views, inventory]
  have arrays (index : Fin 2) :
      (first.tables[index.val]'(by omega)).table = (second.tables[index.val]'(by omega)).table := by
    have same := congrArg (fun arrays => arrays[index.val]?) rows
    simpa only [List.getElem?_map, List.getElem?_take, ite_eq_left index.isLt,
      List.getElem?_eq_getElem (by omega : index.val < first.tables.length),
      List.getElem?_eq_getElem (by omega : index.val < second.tables.length),
      Option.map_some, Option.some.injEq] using same
  simp only [records_eq, arrays ⟨0, by decide⟩, arrays ⟨1, by decide⟩]
  dsimp only [activity, Expression.eval, Environment.fromArray]
  rfl

end SP1Clean.Soundness.FinalMemoryEnsemble
