import SP1Clean.Soundness.OrderedMemoryEnsemble
import ToClean.Air.ChannelClosure
import ToClean.Air.ComponentOutput
import SP1Clean.Proofs.Chips.OrderedSnapshotProvider

/-! # Physical source inventory for an arbitrary local snapshot

The register and RAM tables authenticate values from one fixed source snapshot. A terminal table
closes their private address-order chain. The shared ordered-inventory theorems recover distinct
locations and the exact Memory ledger; no separate lookup list or witness-selected interpretation
is introduced. Complete machine-state binding and source-time admissibility belong to grounding.
-/

namespace SP1Clean.Soundness.SnapshotMemoryEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def channelName : String := "SP1NativeMemoryInitOrder"

def registerView (snapshot : MemorySnapshot) :
    TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide)
    (MemoryBoundary.SnapshotSpec snapshot) (SnapshotRegisterProvider.circuit snapshot)
    (fun _ _ _ valid => valid.1) (fun _ valid => valid.canonical) (by
      simp [GeneralFormalCircuit.channels, SnapshotRegisterProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel])

def ramView (snapshot : MemorySnapshot) :
    TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.providerView channelName (by decide)
    (MemoryBoundary.SnapshotSpec snapshot) (SnapshotRamProvider.circuit snapshot)
    (fun _ _ _ valid => valid.1) (fun _ valid => valid.canonical) (by
      simp [GeneralFormalCircuit.channels, SnapshotRamProvider.circuit, circuit_norm,
        OrderedBoundary.channel, channelName, memoryChannel, byteChannel])

def terminalView : TransitionView (OrderedBoundary.channel (p := p) channelName) :=
  OrderedMemoryEnsemble.terminalView channelName (by decide)

inductive TableId where
  | registers | ram | terminal
deriving DecidableEq

def viewFor (snapshot : MemorySnapshot) : TableId →
    TransitionView (OrderedBoundary.channel (p := p) channelName)
  | .registers => registerView snapshot
  | .ram => ramView snapshot
  | .terminal => terminalView

def recordFor (snapshot : MemorySnapshot) : TableId → Environment (ZMod p) → Option (MemoryMsg (ZMod p))
  | .registers, env => some ((registerView snapshot).component.rowOutput env)
  | .ram, env => some ((ramView snapshot).component.rowOutput env)
  | .terminal, _ => none

/-- All inventory obligations are proved from the actual components and their output decoders. -/
def inventory (snapshot : MemorySnapshot) :
    OrderedMemoryEnsemble.Inventory channelName (MemoryBoundary.SnapshotSpec (p := p) snapshot) where
  Index := TableId
  tableIds := [.registers, .ram, .terminal]
  viewFor := viewFor snapshot
  recordFor := recordFor snapshot
  strict := by
    intro id env valid
    cases id
    · exact valid.2.1.2.2
    · exact valid.2.1.2.2
    · exact valid.2
  recordFor_spec := by
    intro id env valid record found
    cases id
    · obtain rfl := Option.some.inj found
      exact ⟨valid.1, valid.2.2⟩
    · obtain rfl := Option.some.inj found
      exact ⟨valid.1, valid.2.2⟩
    · contradiction

theorem views_eq (snapshot : MemorySnapshot) :
    (inventory (p := p) snapshot).views = [registerView snapshot, ramView snapshot, terminalView] := rfl

/-- Each decoded record is precisely the unit-multiplicity push from its physical provider row. -/
theorem recordFor_interactions (snapshot : MemorySnapshot) (id : TableId) (env : Environment (ZMod p)) :
    (viewFor snapshot id).component.operations.interactionValuesWith memoryChannel.toRaw env =
      ((recordFor snapshot id env).toList).map memoryChannel.pushedValue := by
  cases id
  · change (registerView snapshot).component.operations.interactionValuesWith memoryChannel.toRaw env = _
    simp only [recordFor, registerView, OrderedMemoryEnsemble.providerView,
      Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations,
      OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [SnapshotRegisterProvider.circuit]
    rw [SnapshotRegisterProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Option.toList_some,
      Component.rowOutput_mk, FormalCircuitBase.output_def, OrderedMemoryProvider.elaborated,
      SnapshotRegisterProvider.elaborated]
  · change (ramView snapshot).component.operations.interactionValuesWith memoryChannel.toRaw env = _
    simp only [recordFor, ramView,
      OrderedMemoryEnsemble.providerView, Operations.interactionValuesWith,
      Component.interactionsWith_eq, Component.rowOperations, OrderedMemoryProvider.circuit]
    rw [OrderedMemoryProvider.main_memory_interactions]
    simp only [SnapshotRamProvider.circuit]
    rw [SnapshotRamProvider.main_memory_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Option.toList_some,
      Component.rowOutput_mk, FormalCircuitBase.output_def, OrderedMemoryProvider.elaborated]
  · exact OrderedMemoryEnsemble.terminalView_memory_interactions _ (by decide) env

/-- Source-provider semantics follow from raw constraints and the Byte guarantees alone.
Memory currency is an output of subsequent grounding, never a provider soundness premise. -/
theorem view_spec (snapshot : MemorySnapshot) (id : TableId) (env : Environment (ZMod p))
    (constraints : (viewFor snapshot id).component.operations.ConstraintsHold env)
    (byte : (viewFor snapshot id).component.operations.ChannelGuarantees byteChannel.toRaw env) :
    (viewFor snapshot id).component.Spec env := by
  have assumptions : (viewFor snapshot id).component.Assumptions env := by cases id <;> trivial
  have channels : (viewFor (p := p) snapshot id).component.circuit.channelsWithGuarantees ⊆
      [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw] := by
    cases id
    · change [byteChannel.toRaw, (OrderedBoundary.channel channelName).toRaw,
        byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw] ⊆ _
      simp
    · change (List.replicate 42 byteChannel.toRaw ++
        [(OrderedBoundary.channel channelName).toRaw] ++ List.replicate 4 byteChannel.toRaw) ⊆ _
      simp
    · exact List.Subset.refl _
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ ((viewFor snapshot id).component.inChannelsOrGuarantees env)]
  intro channel member
  rcases List.mem_cons.mp (channels member) with rfl | member
  · exact byte
  · obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [OrderedBoundary.channel, Channel.toRaw]) _ _

end SP1Clean.Soundness.SnapshotMemoryEnsemble
