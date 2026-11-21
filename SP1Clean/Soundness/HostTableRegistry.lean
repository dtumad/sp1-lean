import SP1Clean.Soundness.HostHintQueueBoundary
import ToClean.Air.TableSlot

/-! # Registered positions of native host component blocks

The source-backed registration has one ordered component list. Bank references name their
actual receiver or terminal component and remain valid when resource blocks are appended.
The installed reference accounts for the protected CPU prefix and its HALT replacement once;
consumers read original tables through `TableSlot`, without maintaining their own offsets.
-/

namespace SP1Clean.Soundness.HostTableRegistry

open Circuit Air.Flat Semantics HostHintReadLocal HostHintReadHandoff HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {extra : List (Component (ZMod p))}

local instance registryLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Existing receivers and source resources followed by the registered extension block. -/
def auxiliary (hints : List Bytes) (extra : List (Component (ZMod p))) : List (Component (ZMod p)) :=
  (receiver :: HostCallReceivers.available).map (·.component) ++
    (wordResources ++ (sourceResources hints ++ extra))

/-- The installed physical suffix has exactly the registered host components, in order. -/
theorem auxiliary_components {image : ProgramImage} {source : ExecutionSnapshot}
    {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
    {channels : List (RawChannel (ZMod p))}
    [sourceRegistration : HostFinalMemory.Registration image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels]
  {sourceNames : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints)}
    (witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels sourceNames) :
    (witness.tables.drop 63).map (·.component) = auxiliary source.host.io.hints extra := by
  have components := HostLocalCore.auxiliaryTables_components (HostHintQueueBoundary.projected witness)
  change ((HostHintQueueBoundary.projected witness).tables.drop 63).map (·.component) =
    auxiliary source.host.io.hints extra at components
  rw [HostHintQueueBoundary.projected_drop witness 63 (by decide)] at components
  exact components

/-- Length of the complete host block, including all appended resources. -/
theorem auxiliary_length (hints : List Bytes) (extra : List (Component (ZMod p))) :
    (auxiliary (p := p) hints extra).length = 31 + extra.length := by
  simp only [auxiliary, List.length_append]
  change 21 + (2 + (8 + extra.length)) = _
  omega

/-- Physical bank position inside the host block, including its administrative terminal. -/
def bankPosition (deferred : Bool) : Index → ℕ
  | some slot => (if deferred then 11 else 3) + slot.val
  | none => if deferred then 26 else 25

/-- Every bank position lies in the registered source-backed block. -/
theorem bankPosition_lt (deferred : Bool) (index : Index) : bankPosition deferred index < 27 := by
  cases index with
  | none => cases deferred <;> decide
  | some slot => have := slot.isLt; cases deferred <;> simp only [bankPosition, Bool.false_eq_true,
      ite_false, ite_true] <;> omega

/-- Typed receiver and terminal references, independent of the enclosing CPU prefix. -/
def bankSlot (hints : List Bytes) (extra : List (Component (ZMod p))) (deferred : Bool) (index : Index) :
    TableSlot (auxiliary (p := p) hints extra) (view deferred index).component where
  index := ⟨bankPosition deferred index, by
    rw [auxiliary_length]
    have bound := bankPosition_lt deferred index
    omega⟩
  component_eq := by
    cases index with
    | none => cases deferred <;> rfl
    | some slot => cases deferred <;> fin_cases slot <;> rfl

/-- Typed bank registration in the actual boundary-installed local ensemble. -/
def installedBankSlot (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (extra : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    [sourceRegistration : HostFinalMemory.Registration image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels]
  {sourceNames : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints)} (deferred : Bool) (index : Index) :
    TableSlot (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints ++ extra) channels sourceNames sourceRegistration.unique sourceRegistration.tables sourceRegistration.boundary).tables (view deferred index).component :=
  ((bankSlot source.host.io.hints extra deferred index).appendRight
    ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer)).setOther 57
    HaltPaddingChip.component (by
      change 57 ≠ ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
        bankPosition deferred index
      rw [List.length_set, ProtectedLocalCore.tables_length]
      omega)

/-- The installed position is the original host-block position plus its CPU prefix. -/
theorem installedBankSlot_index (image : ProgramImage) (source : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (extra : List (Component (ZMod p)))
    (channels : List (RawChannel (ZMod p)))
    [sourceRegistration : HostFinalMemory.Registration image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels]
  {sourceNames : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints)} (deferred : Bool) (index : Index) :
    (installedBankSlot image source final bankFinal extra channels (sourceNames := sourceNames) deferred index).index.val =
      63 + bankPosition deferred index := by
  change ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer).length +
    bankPosition deferred index = _
  rw [List.length_set, ProtectedLocalCore.tables_length]

end SP1Clean.Soundness.HostTableRegistry
