import SP1Clean.Soundness.OrderedBoundaryEnsemble
import SP1Clean.Proofs.Chips.OrderedInitialProvider
import SP1Clean.Native.Operations.OrderedBoundaryEnd
import ToMathlib.ListFilterMap

/-! # Native initialization tables with fixed control endpoints

Register and RAM initialization share one private ordering channel. The fixed endpoints are
zero and `2^48 + 1`; a terminal table closes the chain after the last address. The transition
views below are proved against the actual Clean circuits. Auxiliary tables may close Memory
and Byte interactions, but may not contribute to this private ordering channel.

This ensemble is an initialization subsystem for the native core. Integrating its authenticated
records into the instruction grounding argument remains separate from its inventory theorem.
-/

namespace SP1Clean.Soundness.InitialMemoryEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def startKey : Word (ZMod p) := #v[0, 0, 0, 0]
def endKey : Word (ZMod p) := #v[1, 0, 0, 1]

omit [Fact (2 ^ 17 < p)] in
theorem startKey_toNat : Word.toNat (startKey (p := p)) = 0 := by
  simp [startKey, Word.toNat]

omit [Fact (2 ^ 17 < p)] in
theorem endKey_toNat : Word.toNat (endKey (p := p)) = 2 ^ 48 + 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
  norm_num [endKey, Word.toNat, ZMod.val_one]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_previous {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedInitialProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.previous = (Eval.eval env input).link.previous := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_current {Payload : TypeMap} [ProvableType Payload]
    (env : Environment (ZMod p)) (input : Var (OrderedInitialProvider.Inputs Payload) (ZMod p)) :
    Eval.eval env input.link.current = (Eval.eval env input).link.current := by
  rcases input with ⟨payload, previous, current, comparison⟩
  simp only [circuit_norm]

def providerView {Payload : TypeMap} [ProvableType Payload] (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output)
    (privateChannel : (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ provider.channels) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) where
  component := ⟨OrderedInitialProvider.circuit OrderedInitialProvider.channelName image provider binds⟩
  edge env :=
    let input := valueFromOffset (OrderedInitialProvider.Inputs Payload) 0 env
    (input.link.previous, input.link.current)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedInitialProvider.circuit]
    rw [OrderedInitialProvider.main_interactions _ (by decide) provider privateChannel]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_current, ProvableType.eval_varFromOffset]
    rfl

def registerView (image : ProgramImage) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  providerView image (InitialRegisterProvider.circuit image) (fun _ _ _ valid => valid.1) (by
    simp [GeneralFormalCircuit.channels, InitialRegisterProvider.circuit, circuit_norm,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, memoryChannel])

def ramView (image : ProgramImage) :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) :=
  providerView image (InitialRamProvider.circuit image) (fun _ _ _ valid => valid.1) (by
    simp [GeneralFormalCircuit.channels, InitialRamProvider.circuit, circuit_norm,
      OrderedBoundary.channel, OrderedInitialProvider.channelName, memoryChannel, byteChannel])

omit [Fact (2 ^ 17 < p)] in
private theorem eval_terminal_previous (env : Environment (ZMod p))
    (input : Var OrderedBoundary.TerminalInputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨previous, comparison⟩
  simp only [circuit_norm]

def terminalView :
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName) where
  component := ⟨OrderedBoundaryEnd.circuit OrderedInitialProvider.channelName endKey⟩
  edge env := ((valueFromOffset OrderedBoundary.TerminalInputs 0 env).previous, endKey)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, OrderedBoundaryEnd.circuit]
    change ((OrderedBoundaryEnd.main OrderedInitialProvider.channelName endKey
      (varFromOffset OrderedBoundary.TerminalInputs 0)).operations
      (size OrderedBoundary.TerminalInputs)).interactionValuesWith _ env = _
    rw [OrderedBoundaryEnd.interactionValues _ (by decide)]
    simp only [eval_terminal_previous, ProvableType.eval_varFromOffset]
    rfl

/-- These three components own the initialization ordering channel. -/
def views (image : ProgramImage) := [registerView (p := p) image, ramView image, terminalView]

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def tableIds : List TableId := [.registers, .ram, .terminal]

def viewFor (image : ProgramImage) : TableId →
    TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName)
  | .registers => registerView image
  | .ram => ramView image
  | .terminal => terminalView

theorem views_eq_map (image : ProgramImage) : views (p := p) image = tableIds.map (viewFor image) := rfl

def ensemble (image : ProgramImage) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) unit :=
  OrderedBoundaryEnsemble.ensemble OrderedInitialProvider.channelName startKey endKey
    (views image) auxiliary channels

private theorem providerView_strict {Payload : TypeMap} [ProvableType Payload] (image : ProgramImage)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → MemoryBoundary.InitialSpec image output)
    (privateChannel : (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ provider.channels)
    (env : Environment (ZMod p))
    (valid : (providerView image provider binds privateChannel).component.Spec env) :
    Word.toNat ((providerView image provider binds privateChannel).edge env).1 <
      Word.toNat ((providerView image provider binds privateChannel).edge env).2 :=
  valid.2.1.2.2

theorem views_strict (image : ProgramImage)
    (view : TransitionView (OrderedBoundary.channel (p := p) OrderedInitialProvider.channelName))
    (member : view ∈ views image) (env : Environment (ZMod p)) (valid : view.component.Spec env) :
    Word.toNat (view.edge env).1 < Word.toNat (view.edge env).2 := by
  simp only [views, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact providerView_strict image _ _ _ env valid
  · exact providerView_strict image _ _ _ env valid
  · exact valid.2

/-- The initialization inventory has no repeated current key, even across register and RAM
tables. The inputs are actual Clean balance and local table specifications, not a uniqueness
or endpoint-binding assumption. -/
theorem keys_nodup (image : ProgramImage) (auxiliary : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    (witness : EnsembleWitness (ensemble image auxiliary channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((OrderedBoundaryEnsemble.rows witness).map fun row => Word.toNat (row.1.edge row.2).2).Nodup := by
  exact OrderedBoundaryEnsemble.keys_nodup_of_specs witness privateChannel
    (views_strict image) valid balanced

/-- Recover a provider's returned record using Clean's own physical-row output decoder. -/
def recordFor (image : ProgramImage) (id : TableId) (env : Environment (ZMod p)) :
    Option (MemoryMsg (ZMod p)) :=
  match id with
  | .registers => some ((⟨OrderedInitialProvider.registerCircuit image⟩ : Component (ZMod p)).rowOutput env)
  | .ram => some ((⟨OrderedInitialProvider.ramCircuit image⟩ : Component (ZMod p)).rowOutput env)
  | .terminal => none

theorem recordFor_spec (image : ProgramImage) (id : TableId) (env : Environment (ZMod p))
    (valid : (viewFor image id).component.Spec env) (record : MemoryMsg (ZMod p))
    (found : recordFor image id env = some record) :
    MemoryBoundary.InitialSpec image record ∧
      Word.toNat ((viewFor image id).edge env).2 = (MemoryMsg.locOf record).busAddress + 1 := by
  cases id with
  | registers =>
    obtain rfl := Option.some.inj found
    exact ⟨valid.1, valid.2.2⟩
  | ram =>
    obtain rfl := Option.some.inj found
    exact ⟨valid.1, valid.2.2⟩
  | terminal => contradiction

variable {image : ProgramImage} {auxiliary : List (Component (ZMod p))}
variable {channels : List (RawChannel (ZMod p))}

def indexedRows (witness : EnsembleWitness (ensemble image auxiliary channels)) :=
  TransitionView.readIndexedRows tableIds (witness.tables.take (views (p := p) image).length)

def records (witness : EnsembleWitness (ensemble image auxiliary channels)) : List (MemoryMsg (ZMod p)) :=
  (indexedRows witness).filterMap fun row => recordFor image row.1 row.2

theorem indexedRows_spec (witness : EnsembleWitness (ensemble image auxiliary channels))
    (valid : witness.Spec) :
    ∀ row ∈ indexedRows witness, (viewFor image row.1).component.Spec row.2 := by
  unfold indexedRows
  apply TransitionView.readIndexedRows_spec tableIds (viewFor image) _
  · rw [← views_eq_map]
    exact OrderedBoundaryEnsemble.tables_aligned witness
  · intro table member
    exact valid table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take member))

/-- Every decoded provider record carries the authentic boot value at its canonical location. -/
theorem records_authentic (witness : EnsembleWitness (ensemble image auxiliary channels))
    (valid : witness.Spec) : ∀ record ∈ records witness, MemoryBoundary.InitialSpec image record := by
  intro record member
  obtain ⟨row, member, found⟩ := List.mem_filterMap.mp member
  exact (recordFor_spec image row.1 row.2 (indexedRows_spec witness valid row member) record found).1

/-- The combined register/RAM provider inventory is unique by decoded memory location.
This follows from actual control balance, even when the physical rows are permuted. -/
theorem records_locations_nodup (witness : EnsembleWitness (ensemble image auxiliary channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel OrderedInitialProvider.channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((records witness).map MemoryMsg.locOf).Nodup := by
  have unique := keys_nodup image auxiliary channels witness privateChannel valid balanced
  have indexed := TransitionView.readIndexedRows_keys_nodup tableIds (viewFor image) _ Word.toNat
    (views image) (views_eq_map image) unique
  have decoded := List.nodup_filterMap_of_nodup_map (indexedRows witness)
    (fun row => Word.toNat ((viewFor image row.1).edge row.2).2)
    (fun row => (recordFor image row.1 row.2).map MemoryMsg.locOf)
    (fun loc => loc.busAddress + 1) indexed (by
      intro row member loc found
      obtain ⟨record, decodedRecord, rfl⟩ := Option.map_eq_some_iff.mp found
      exact (recordFor_spec image row.1 row.2
        (indexedRows_spec witness valid row member) record decodedRecord).2)
  simpa only [records, List.map_filterMap, Function.comp_def] using decoded

end SP1Clean.Soundness.InitialMemoryEnsemble
