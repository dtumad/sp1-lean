import SP1Clean.Soundness.OrderedMemoryEnsemble
import SP1Clean.Proofs.Chips.OrderedFinalProvider

/-! # Native final-memory inventory

Final register and RAM rows share a private control channel with fixed endpoints. Every physical
provider row pulls one canonical Memory record. The shared inventory proof excludes repeated
locations across both tables. Connecting this inventory to the timed machine establishes that
these are the final values; that claim is not a local finalizer assumption.
-/

namespace SP1Clean.Soundness.FinalMemoryEnsemble

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

open SP1Clean.OrderedFinalProvider

def registerView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.FinalSpec
    FinalRegisterProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid.1) (by
      simp [GeneralFormalCircuit.channels, FinalRegisterProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel])

def ramView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide) MemoryBoundary.FinalSpec
    FinalRamProvider.circuit (fun _ _ _ valid => valid.1) (fun _ valid => valid.1) (by
      simp [GeneralFormalCircuit.channels, FinalRamProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel, byteChannel])

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def viewFor : TableId → TransitionView (OrderedBoundary.channel (p := p) channelName)
  | .registers => registerView
  | .ram => ramView
  | .terminal => OrderedMemoryEnsemble.terminalView channelName (by decide)

def recordFor (id : TableId) (env : Environment (ZMod p)) : Option (MemoryMsg (ZMod p)) :=
  match id with
  | .registers => some ((⟨registerCircuit⟩ : Component (ZMod p)).rowOutput env)
  | .ram => some ((⟨ramCircuit⟩ : Component (ZMod p)).rowOutput env)
  | .terminal => none

def inventory : OrderedMemoryEnsemble.Inventory channelName (MemoryBoundary.FinalSpec (p := p)) where
  Index := TableId
  tableIds := [.registers, .ram, .terminal]
  viewFor := viewFor
  recordFor := recordFor
  strict := by
    intro id env valid
    cases id with
    | registers => exact valid.2.1.2.2
    | ram => exact valid.2.1.2.2
    | terminal => exact valid.2
  recordFor_spec := by
    intro id env valid record found
    cases id with
    | registers =>
      obtain rfl := Option.some.inj found
      exact ⟨valid.1, valid.2.2⟩
    | ram =>
      obtain rfl := Option.some.inj found
      exact ⟨valid.1, valid.2.2⟩
    | terminal => contradiction

def ensemble (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p))) :=
  inventory.ensemble auxiliary channels

variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

def records (witness : EnsembleWitness (ensemble auxiliary channels)) := inventory.records witness

theorem records_valid (witness : EnsembleWitness (ensemble auxiliary channels))
    (valid : witness.Spec) : ∀ record ∈ records witness, MemoryBoundary.FinalSpec record :=
  inventory.records_valid witness valid

theorem records_locations_nodup (witness : EnsembleWitness (ensemble auxiliary channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel channelName).toRaw ∉ component.circuit.channels)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((records witness).map MemoryMsg.locOf).Nodup :=
  inventory.records_locations_nodup witness privateChannel valid balanced

/-- The finite record decoder agrees exactly with each table's physical Memory interactions. -/
theorem recordFor_interactions (id : TableId) (env : Environment (ZMod p)) :
    (viewFor id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((recordFor id env).toList).map memoryChannel.pulledValue := by
  cases id with
  | registers =>
    simp only [viewFor, registerView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRegisterProvider.circuit]
    rw [FinalRegisterProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled]
    simp only [recordFor, Option.toList_some, List.map_cons, List.map_nil, Component.rowOutput,
      OrderedFinalProvider.registerCircuit, OrderedMemoryProvider.circuit, FinalRegisterProvider.circuit,
      OrderedMemoryProvider.elaborated, FinalRegisterProvider.elaborated, circuit_norm]
  | ram =>
    simp only [viewFor, ramView, OrderedMemoryEnsemble.providerView,
        Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
        OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [FinalRamProvider.circuit]
    rw [FinalRamProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled]
    simp only [recordFor, Option.toList_some, List.map_cons, List.map_nil, Component.rowOutput,
      OrderedFinalProvider.ramCircuit, OrderedMemoryProvider.circuit, FinalRamProvider.circuit,
      OrderedMemoryProvider.elaborated, FinalRamProvider.elaborated, circuit_norm]
  | terminal =>
    exact OrderedMemoryEnsemble.terminalView_memory_interactions _ (by decide) env

/-- The physical boundary tables emit precisely the decoded records, with unit multiplicity. -/
theorem memory_interactions_eq (witness : EnsembleWitness (ensemble auxiliary channels)) :
    (witness.tables.take (inventory (p := p)).views.length).flatMap (·.interactionsWith memoryChannel.toRaw) =
      (records witness).map memoryChannel.pulledValue := by
  exact inventory.memory_interactions_eq witness memoryChannel.pulledValue recordFor_interactions

end SP1Clean.Soundness.FinalMemoryEnsemble
