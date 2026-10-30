import SP1Clean.Soundness.HostHintQueueBoundary
import ToClean.Air.TableSlot

/-! # Registered positions of native host component blocks

The source-backed registration has one ordered component list. Bank references name their
actual receiver or terminal component and remain valid when resource blocks are appended.
The installed reference accounts for the protected CPU prefix and its HALT replacement once;
consumers read original tables through `TableSlot`, without maintaining their own offsets.
-/

namespace SP1Clean.Soundness.HostTableRegistry

open Circuit Air.Flat Model.Core HostHintReadLocal HostHintReadHandoff HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {outgoing : MemorySnapshot}

local instance registryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Existing receiver, source-resource and target-validator blocks, in their physical
registration order. -/
def auxiliary (hints : List Bytes) (outgoing : MemorySnapshot) : List (Component (ZMod p)) :=
  (receiver :: HostCallReceivers.available).map (·.component) ++
    (wordResources ++ (sourceResources hints ++ FinalMemoryChecks.checkTables outgoing))

/-- The installed physical suffix has exactly the registered host components, in order. -/
theorem auxiliary_components {image : ProgramImage} {source : ExecutionSnapshot}
    {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal
      HostCallReceivers.available (sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables outgoing) channels
      (HostFinalMemory.source_unique_names image source outgoing))) :
    (witness.tables.drop 63).map (·.component) = auxiliary source.host.io.hints outgoing := by
  have components := HostLocalCore.auxiliaryTables_components (HostHintQueueBoundary.projected witness)
  change ((HostHintQueueBoundary.projected witness).tables.drop 63).map (·.component) =
    auxiliary source.host.io.hints outgoing at components
  rw [HostHintQueueBoundary.projected_drop witness 63 (by decide)] at components
  exact components

/-- Number of installed host components before any further resource extension. -/
theorem auxiliary_length (hints : List Bytes) (outgoing : MemorySnapshot) :
    (auxiliary (p := p) hints outgoing).length = 31 := rfl

/-- Physical bank position inside the host block, including its administrative terminal. -/
def bankPosition (deferred : Bool) : Index → ℕ
  | some slot => (if deferred then 11 else 3) + slot.val
  | none => if deferred then 26 else 25

/-- Every bank position lies in the registered source-backed block. -/
theorem bankPosition_lt (deferred : Bool) (index : Index) : bankPosition deferred index < 27 := by
  cases index with
  | none => cases deferred <;> decide
  | some slot => have := slot.isLt; cases deferred <;> simp only [bankPosition, Bool.false_eq_true,
      if_false, if_true] <;> omega

/-- Typed receiver and terminal references, independent of the enclosing CPU prefix. -/
def bankSlot (hints : List Bytes) (outgoing : MemorySnapshot) (deferred : Bool) (index : Index) :
    TableSlot (auxiliary (p := p) hints outgoing) (view deferred index).component where
  index := ⟨bankPosition deferred index, by
    rw [auxiliary_length]; exact Nat.lt_of_lt_of_le (bankPosition_lt deferred index) (by decide)⟩
  component_eq := by
    cases index with
    | none => cases deferred <;> rfl
    | some slot => cases deferred <;> fin_cases slot <;> rfl

/-- Typed bank registration in the actual boundary-installed local ensemble. -/
def installedBankSlot (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (outgoing : MemorySnapshot)
    (channels : List (RawChannel (ZMod p))) (deferred : Bool) (index : Index) :
    TableSlot (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables outgoing) channels (HostFinalMemory.source_unique_names image source outgoing)).tables (view deferred index).component :=
  ((bankSlot source.host.io.hints outgoing deferred index).appendRight
    ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer)).setOther 57
    HaltPaddingChip.component (by
      change 57 ≠ ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
        bankPosition deferred index
      rw [List.length_set, ProtectedLocalCore.tables_length]
      omega)

/-- The installed position is the original host-block position plus its CPU prefix. -/
theorem installedBankSlot_index (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (outgoing : MemorySnapshot)
    (channels : List (RawChannel (ZMod p))) (deferred : Bool) (index : Index) :
    (installedBankSlot image source final bankFinal outgoing channels deferred index).index.val =
      63 + bankPosition deferred index := by
  change ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
    bankPosition deferred index = _
  rw [List.length_set, ProtectedLocalCore.tables_length]

end SP1Clean.Soundness.HostTableRegistry
