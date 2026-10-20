import SP1Clean.Soundness.OrderedBoundaryEnsemble
import SP1Clean.Proofs.Chips.OrderedMemoryProvider
import SP1Clean.Native.Operations.OrderedBoundaryEnd
import ToMathlib.ListFilterMap

/-! # Ordered native memory inventories

Initialization and finalization share fixed endpoints, physical transition views, and the same
location-uniqueness argument. An inventory registers its actual components and record decoder once;
its local correctness fields are proofs about those components, not assumptions on a witness.
-/

namespace SP1Clean.Soundness.OrderedMemoryEnsemble

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def startKey : Word (ZMod p) := #v[0, 0, 0, 0]
def endKey : Word (ZMod p) := #v[1, 0, 0, 1]

omit [Fact (2 ^ 17 < p)] in
theorem startKey_toNat : Word.toNat (startKey (p := p)) = 0 := by
  simp [startKey, Word.toNat]

omit [Fact (2 ^ 17 < p)] in
theorem endKey_toNat : Word.toNat (endKey (p := p)) = 2 ^ 48 + 1 := by
  have : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
  norm_num [endKey, Word.toNat, ZMod.val_one]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_previous {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedMemoryProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.previous = (Eval.eval env input).link.previous := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_current {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedMemoryProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.current = (Eval.eval env input).link.current := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_activity {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedMemoryProvider.RowInput Payload) (ZMod p)) :
    env input.2 = (Eval.eval env input).2 := by
  simp only [circuit_norm]

def providerView {Payload : TypeMap} [ProvableType Payload] (name : String) (distinct : name ≠ "SP1Byte")
    (recordSpec : MemoryMsg (ZMod p) → Prop)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg) [Guarded.Supported provider]
    (binds : ∀ input output data, provider.Spec input output data → recordSpec output)
    (canonical : ∀ record, recordSpec record → MemoryBoundary.CanonicalSpec record)
    (privateChannel : (OrderedBoundary.channel name).toRaw ∉ provider.channels) :
    TransitionView (OrderedBoundary.channel (p := p) name) where
  component := {
    circuit := OrderedMemoryProvider.circuit name recordSpec provider binds canonical
    Assumptions := (OrderedMemoryProvider.circuit name recordSpec provider binds canonical).Assumptions
  }
  activity := (varFromOffset (OrderedMemoryProvider.RowInput Payload) 0).2
  edge env :=
    let input := valueFromOffset (OrderedMemoryProvider.RowInput Payload) 0 env
    (input.1.link.previous, input.1.link.current)
  activity_binary := by
    intro env valid
    rw [eval_activity, eval_varFromOffset_valueFromOffset]
    exact valid.1
  activity_of_constraints := by
    intro env valid
    rw [Component.constraintsHold_iff] at valid
    exact Guarded.activity_of_constraints
      (OrderedMemoryProvider.activeCircuit name recordSpec provider binds canonical) inferInstance
      (varFromOffset (OrderedMemoryProvider.RowInput Payload) 0)
      (size (OrderedMemoryProvider.RowInput Payload)) env valid
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedMemoryProvider.circuit, Guarded.circuit]
    rw [Guarded.main_interactionsWith]
    simp only [OrderedMemoryProvider.activeCircuit]
    rw [OrderedMemoryProvider.main_interactions _ distinct provider privateChannel]
    simp only [List.map_cons, List.map_nil,
      AbstractInteraction.eval_guard, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_current]
    simp [Channel.pulledValue, Channel.pushedValue, Channel.pulledIfValue, Channel.pushedIfValue,
      circuit_norm]
    have decoded := eval_varFromOffset_valueFromOffset (OrderedMemoryProvider.RowInput Payload) 0 env
    rw [CircuitType.eval_var_provablePair] at decoded
    have payload := congrArg Prod.fst decoded
    simp only [circuit_norm] at payload
    exact ⟨congrArg (fun input => toElements input.link.previous) payload,
      congrArg (fun input => toElements input.link.current) payload⟩

omit [Fact (2 ^ 17 < p)] in
/-- Reading a provider's physical activity agrees with the decoded input selector. -/
theorem active_input {Payload : TypeMap} [ProvableType Payload] {env : Environment (ZMod p)}
    (active : env (varFromOffset (OrderedMemoryProvider.RowInput Payload) 0).2 = 1) :
    (valueFromOffset (OrderedMemoryProvider.RowInput Payload) 0 env).2 = (1 : ZMod p) := by
  simpa only [eval_activity, eval_varFromOffset_valueFromOffset] using active

omit [Fact (2 ^ 17 < p)] in
private theorem eval_terminal_previous (env : Environment (ZMod p))
    (input : Var OrderedBoundary.TerminalInputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨previous, comparison⟩
  simp only [circuit_norm]

def terminalView (name : String) (distinct : name ≠ "SP1Byte") :
    TransitionView (OrderedBoundary.channel (p := p) name) where
  component := { circuit := OrderedBoundaryEnd.circuit name endKey, Assumptions := (OrderedBoundaryEnd.circuit name endKey).Assumptions }
  edge env := ((valueFromOffset OrderedBoundary.TerminalInputs 0 env).previous, endKey)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedBoundaryEnd.circuit]
    change ((OrderedBoundaryEnd.main name endKey
      (varFromOffset OrderedBoundary.TerminalInputs 0)).operations
      (size OrderedBoundary.TerminalInputs)).interactionValuesWith _ env = _
    rw [OrderedBoundaryEnd.interactionValues _ distinct]
    simp only [eval_terminal_previous, ProvableType.eval_varFromOffset]
    rfl

theorem terminalView_memory_interactions (name : String) (distinct : name ≠ "SP1Byte")
    (env : Environment (ZMod p)) :
    (terminalView name distinct).component.operations.interactionValuesWith memoryChannel.toRaw env = [] := by
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundaryEnd.circuit name (endKey (p := p))).base memoryChannel.toRaw
    (varFromOffset OrderedBoundary.TerminalInputs 0) (size OrderedBoundary.TerminalInputs) (by
      simp [OrderedBoundaryEnd.circuit, circuit_norm, OrderedBoundary.channel, memoryChannel, byteChannel])
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
    Component.rowOperations, terminalView, OrderedBoundaryEnd.circuit] at empty ⊢
  rw [empty]
  rfl

/-- Static proof-bearing registry of providers and their terminal component. -/
structure Inventory (name : String) (recordSpec : MemoryMsg (ZMod p) → Prop) where
  Index : Type
  tableIds : List Index
  viewFor : Index → TransitionView (OrderedBoundary.channel (p := p) name)
  recordFor : Index → Environment (ZMod p) → Option (MemoryMsg (ZMod p))
  strict : ∀ id env, (viewFor id).component.Spec env → env (viewFor id).activity = 1 →
    Word.toNat ((viewFor id).edge env).1 < Word.toNat ((viewFor id).edge env).2
  recordFor_spec : ∀ id env, (viewFor id).component.Spec env → env (viewFor id).activity = 1 →
    ∀ record, recordFor id env = some record → recordSpec record ∧
      Word.toNat ((viewFor id).edge env).2 = (MemoryMsg.locOf record).busAddress + 1

namespace Inventory

variable {name : String} {recordSpec : MemoryMsg (ZMod p) → Prop}

def views (inventory : Inventory name recordSpec) := inventory.tableIds.map inventory.viewFor

def ensemble (inventory : Inventory name recordSpec) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (names : ((inventory.views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup) :
    Ensemble (ZMod p) unit :=
  OrderedBoundaryEnsemble.ensemble name startKey endKey inventory.views auxiliary channels names

variable (inventory : Inventory name recordSpec) {auxiliary : List (Component (ZMod p))}
variable {channels : List (RawChannel (ZMod p))}
variable {names : ((inventory.views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}

/-- All original row environments and registry identities, including padding. -/
def physicalRows (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) :=
  TransitionView.readIndexedRows inventory.tableIds (witness.tables.take inventory.views.length)

/-- Active rows carry semantic memory records; their environments still use canonical table data. -/
def indexedRows (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) :=
  TransitionView.readIndexedActiveRows inventory.tableIds inventory.viewFor
    (witness.tables.take inventory.views.length)

/-- Every physical record occurrence retains its actual activity, including zero. -/
def physicalRecords (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) :
    List (ZMod p × MemoryMsg (ZMod p)) :=
  (inventory.physicalRows witness).filterMap fun row =>
    (inventory.recordFor row.1 row.2).map fun record => (row.2 (inventory.viewFor row.1).activity, record)

def records (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) : List (MemoryMsg (ZMod p)) :=
  (inventory.indexedRows witness).filterMap fun row => inventory.recordFor row.1 row.2

omit [Fact (2 ^ 17 < p)] in
/-- The decoded record inventory is the actual Memory ledger whenever each registered component
has the stated single-record effect. This transport assumes no constraints or semantic facts. -/
theorem memory_interactions_eq (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (effect : ZMod p → MemoryMsg (ZMod p) → Interaction (ZMod p))
    (realizes : ∀ id env, (inventory.viewFor id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((inventory.recordFor id env).toList).map (effect (env (inventory.viewFor id).activity))) :
    (witness.tables.take inventory.views.length).flatMap (·.interactionsWith memoryChannel.toRaw) =
      (inventory.physicalRecords witness).map (fun row => effect row.1 row.2) := by
  have aligned := OrderedBoundaryEnsemble.tables_aligned witness
  change List.Forall₂ _ (inventory.tableIds.map inventory.viewFor) _ at aligned
  rw [List.forall₂_map_left_iff] at aligned
  rw [TransitionView.readIndexedRows_interactions inventory.tableIds
    (fun id => (inventory.viewFor id).component) _ _ aligned]
  simp only [realizes, physicalRecords, physicalRows, List.filterMap_eq_flatMap_toList,
    List.map_flatMap, Option.toList_map, List.map_map, Function.comp_def]


omit [Fact (2 ^ 17 < p)] in
/-- Selecting active records changes neither the physical ledger nor the table data. -/
theorem records_eq_active_physical (witness : EnsembleWitness (inventory.ensemble auxiliary channels names)) :
    inventory.records witness =
      ((inventory.physicalRecords witness).filter fun row => decide (row.1 = 1)).map Prod.snd := by
  simp only [records, indexedRows, TransitionView.readIndexedActiveRows, physicalRecords, physicalRows]
  generalize TransitionView.readIndexedRows inventory.tableIds
    (witness.tables.take inventory.views.length) = entries
  induction entries with
  | nil => rfl
  | cons row entries ih =>
    cases decoded : inventory.recordFor row.1 row.2 <;>
      by_cases active : row.2 (inventory.viewFor row.1).activity = 1 <;>
        simp [decoded, active, ih]

omit [Fact (2 ^ 17 < p)] in
/-- Boolean activity of every physical record follows from its actual table specification. -/
theorem physicalRecords_binary (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec) :
    ∀ row ∈ inventory.physicalRecords witness, row.1 = 0 ∨ row.1 = 1 := by
  intro row rowMem
  obtain ⟨physical, physicalMem, found⟩ := List.mem_filterMap.mp rowMem
  obtain ⟨record, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact (inventory.viewFor physical.1).activity_binary physical.2
    (TransitionView.readIndexedRows_spec inventory.tableIds inventory.viewFor _
      (OrderedBoundaryEnsemble.tables_aligned witness) valid physical physicalMem)

omit [Fact (2 ^ 17 < p)] in
/-- Raw constraints suffice for physical record multiplicities, before channel authentication. -/
theorem physicalRecords_binary_of_constraints
    (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Constraints) :
    ∀ row ∈ inventory.physicalRecords witness, row.1 = 0 ∨ row.1 = 1 := by
  intro row rowMem
  obtain ⟨physical, physicalMem, found⟩ := List.mem_filterMap.mp rowMem
  obtain ⟨record, _, rfl⟩ := Option.map_eq_some_iff.mp found
  have aligned := OrderedBoundaryEnsemble.tables_aligned witness
  change List.Forall₂ _ (inventory.tableIds.map inventory.viewFor) _ at aligned
  rw [List.forall₂_map_left_iff] at aligned
  exact (inventory.viewFor physical.1).activity_of_constraints physical.2
    (TransitionView.readIndexedRows_constraints inventory.tableIds
      (fun id => (inventory.viewFor id).component) _ aligned valid physical physicalMem)

omit [Fact (2 ^ 17 < p)] in
theorem indexedRows_spec_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec) :
    ∀ row ∈ inventory.indexedRows witness, (inventory.viewFor row.1).component.Spec row.2 := by
  apply TransitionView.readIndexedActiveRows_spec inventory.tableIds inventory.viewFor _
  · exact OrderedBoundaryEnsemble.tables_aligned witness
  · exact valid

omit [Fact (2 ^ 17 < p)] in
theorem records_valid_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec) :
    ∀ record ∈ inventory.records witness, recordSpec record := by
  intro record member
  obtain ⟨row, member, found⟩ := List.mem_filterMap.mp member
  exact (inventory.recordFor_spec row.1 row.2
    (inventory.indexedRows_spec_of_tables witness valid row member)
    (TransitionView.mem_readIndexedActiveRows.mp member).2 record found).1

omit [Fact (2 ^ 17 < p)] in
/-- Actual Clean balance forces distinct canonical locations throughout the inventory. -/
theorem records_locations_nodup_of_tables (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (valid : ∀ table ∈ witness.tables.take inventory.views.length, table.Spec)
    (balanced : witness.BalancedChannel (OrderedBoundary.channel name).toRaw) :
    ((inventory.records witness).map MemoryMsg.locOf).Nodup := by
  have unique := OrderedBoundaryEnsemble.keys_nodup_of_tables witness privateChannel (by
    intro view member env spec active
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
    exact inventory.strict id env spec active) valid balanced
  have indexed := TransitionView.readIndexedActiveRows_keys_nodup inventory.tableIds inventory.viewFor _ Word.toNat
    inventory.views rfl unique
  have decoded := List.nodup_filterMap_of_nodup_map (inventory.indexedRows witness)
    (fun row => Word.toNat ((inventory.viewFor row.1).edge row.2).2)
    (fun row => (inventory.recordFor row.1 row.2).map MemoryMsg.locOf)
    (fun loc => loc.busAddress + 1) indexed (by
      intro row member loc found
      obtain ⟨record, decodedRecord, rfl⟩ := Option.map_eq_some_iff.mp found
      exact (inventory.recordFor_spec row.1 row.2
        (inventory.indexedRows_spec_of_tables witness valid row member)
        (TransitionView.mem_readIndexedActiveRows.mp member).2 record decodedRecord).2)
  simpa only [records, List.map_filterMap, Function.comp_def] using decoded

omit [Fact (2 ^ 17 < p)] in
theorem indexedRows_spec (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : witness.Spec) :
    ∀ row ∈ inventory.indexedRows witness, (inventory.viewFor row.1).component.Spec row.2 :=
  inventory.indexedRows_spec_of_tables witness (fun table member =>
    valid.2 table (List.mem_of_mem_take member))

omit [Fact (2 ^ 17 < p)] in
theorem records_valid (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (valid : witness.Spec) : ∀ record ∈ inventory.records witness, recordSpec record :=
  inventory.records_valid_of_tables witness (fun table member =>
    valid.2 table (List.mem_of_mem_take member))

omit [Fact (2 ^ 17 < p)] in
theorem records_locations_nodup (witness : EnsembleWitness (inventory.ensemble auxiliary channels names))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((inventory.records witness).map MemoryMsg.locOf).Nodup :=
  inventory.records_locations_nodup_of_tables witness privateChannel
    (fun table member => valid.2 table (List.mem_of_mem_take member))
    (balanced _ (List.mem_cons_self ..))

end Inventory
end SP1Clean.Soundness.OrderedMemoryEnsemble
