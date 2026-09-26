import SP1Clean.Soundness.HostFinalMemoryTransport
import SP1Clean.Soundness.HostFinalMemoryInventory

/-! # Complete target Memory comparison from raw host acceptance

The actual host witness supplies Byte closure and all three private receipt balances.
The existing boundary theorem then checks the complete target, including every location
outside the physical final inventory. No endpoint certificate or witness-selected change
inventory is a premise. Full mixed Sail/host endpoint reconstruction remains a later consumer.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- Complete comparison requires only inherited Byte guarantees and the three actual receipt balances. -/
theorem checkFinal_of_channels
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (checked : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    (balances : ∀ channel ∈ privateChannels (p := p), witness.BalancedChannel channel) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply FinalMemoryChecks.checkFinal_of_channels (boundaryWitness witness)
    ⟨by simp, by simp, by simp⟩ (boundaryWitness_constraints witness checked)
    (boundaryWitness_byte witness bytes)
  · intro ram
    have member : (FinalMemoryValue.channel ram).toRaw ∈ privateChannels (p := p) := by
      cases ram <;> simp [privateChannels]
    exact boundaryWitness_balancedChannel witness interface _ member (balances _ member)
  · have member : FinalMemoryChange.channel.toRaw ∈ privateChannels (p := p) := by simp [privateChannels]
    exact boundaryWitness_balancedChannel witness interface _ member (balances _ member)

/-- Complete raw host AIR acceptance implies the existing finite target Memory comparison.
The two interfaces describe fixed installed circuits, never properties of the supplied witness. -/
theorem checkFinal
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : HostHintReadLocal.ExtensionInterface others resources)
    (privacy : PrivateInterface others resources)
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness privacy checked (byte_guarantees witness interface checked (balanced _ ?_))
  · intro channel member
    apply balanced
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [ensemble, ClosedVerifier.install, withReceipts, withRegisters, FinalReceiptEnsemble.install,
        FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, circuit_norm]
  · simp [ensemble, ClosedVerifier.install, withReceipts, withRegisters, FinalReceiptEnsemble.install,
      base, HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble,
      HostLocalHandoff.ensemble, HostLocalCore.ensemble, ProtectedLocalCore.ensemble, LocalCore.ensemble,
      sp1Ensemble_channels]

/-- The concrete six-call registration needs only raw acceptance, with no caller interface proofs. -/
theorem source_checkFinal
    (witness : EnsembleWitness (ensemble image source target final bankFinal HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) channels))
    (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.sail.memorySnapshot.checkFinal target
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true :=
  checkFinal witness (HostHintReadLocal.source_interface source.host.io.hints)
    (source_privacy source.host.io.hints) checked balanced

end SP1Clean.Soundness.HostFinalMemory
