import SP1Clean.Soundness.HostFinalMemoryRegistry

/-! # Static interface for resource tables appended to the source-backed host

The ordered CPU, host receivers, word handlers and source records retain their own channel
occurrences. Additional resource tables may introduce other channels, subject to the registered
names and the local Byte requirements. The installed final-memory validators discharge this
interface from their actual circuits, independently of the witness or the guest execution.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance extensionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Channel names excluded from the resource suffix by the six-handler grounding proof. -/
def groundingChannels : List (RawChannel (ZMod p)) :=
  [stateChannel.toRaw, HostCallChip.channel.toRaw, HintReadWordChip.stateChannel.toRaw,
    HostHintQueue.stateChannel.toRaw, HostHintQueue.nodeChannel.toRaw, HostHintQueue.wordChannel.toRaw,
    memoryChannel.toRaw, programChannel.toRaw, WritePermissionProvider.channel.toRaw, exitChannel.toRaw,
    HostExitBoundary.channel.toRaw, (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw,
    (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw, (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw]

/-- No component of a resource block sends or receives on the named physical channel. -/
def ChannelSilent (components : List (Component (ZMod p))) (channel : RawChannel (ZMod p)) : Bool :=
  components.all (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name)

/-- Static operations and channel declarations sufficient to preserve six-handler grounding. -/
class GroundingResources (extra : List (Component (ZMod p))) : Prop where
  byte : ∀ component ∈ extra, ∀ env, component.operations.ConstraintsHold env →
    component.operations.ChannelRequirements byteChannel.toRaw env
  quiet : ∀ channel ∈ groundingChannels (p := p), ChannelSilent extra channel = true
  sourceMembership : ∀ snapshot, ∀ channel ∈ SnapshotMemoryEnsemble.membershipChannels (p := p) snapshot,
    ChannelSilent extra channel = true
  permissionMembership : ∀ image : ProgramImage, extra.all (fun component =>
    !(component.circuit.channelsWithRequirements.map RawChannel.name).contains (image.writePermissionTable (p := p)).name) = true

variable {extra : List (Component (ZMod p))}

omit [Fact (2 ^ 25 < p)] in
/-- Static name disjointness gives the typed channel exclusion for every physical table. -/
theorem GroundingResources.silent [extension : GroundingResources extra] {channel : RawChannel (ZMod p)}
    (memberChannel : channel ∈ groundingChannels (p := p)) : ∀ component ∈ extra, channel ∉ component.circuit.channels := by
  intro component member used
  have absent := List.all_eq_true.mp (extension.quiet channel memberChannel) component member
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
  contradiction

omit [Fact (2 ^ 25 < p)] in
/-- Append the registered components to any previously checked host extension. -/
theorem GroundingResources.appendInterface (extra : List (Component (ZMod p))) [extension : GroundingResources extra]
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    (interface : HostHintReadLocal.ExtensionInterface others resources) :
    HostHintReadLocal.ExtensionInterface others (resources ++ extra) := by
  apply interface.appendResources
  · exact ⟨extension.byte, GroundingResources.silent (extra := extra) (by simp [groundingChannels])⟩
  · exact GroundingResources.silent (extra := extra) (by simp [groundingChannels])
  · exact GroundingResources.silent (extra := extra) (by simp [groundingChannels])

/-- The source records and appended block supply the installed host extension interface. -/
theorem GroundingResources.sourceInterface (hints : List Bytes) (extra : List (Component (ZMod p)))
    [GroundingResources extra] (includeVerify : Bool := false) :
    HostHintReadLocal.ExtensionInterface (HostCallReceivers.availableFor includeVerify) (HostHintReadLocal.sourceResources hints ++ extra) :=
  GroundingResources.appendInterface extra (HostHintReadLocal.source_interface hints includeVerify)

/-- The released fixed final-memory tables satisfy the resource interface in the installed assembly. -/
instance (target : MemorySnapshot) : GroundingResources (FinalMemoryChecks.checkTables (p := p) target) where
  byte := by
    intro component member env checked
    simp only [FinalMemoryChecks.checkTables, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact HostFinalMemory.not_required _ (by rfl) env checked
  quiet := by
    intro channel member
    simp only [groundingChannels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  sourceMembership := by
    intro snapshot channel member
    simp only [SnapshotMemoryEnsemble.membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [ChannelSilent, Channel.toRaw_name, StaticTable.channel, MemorySnapshot.registerTable, StaticTable.ofRows]
      rfl
    · rfl
  permissionMembership := by
    intro image
    unfold ProgramImage.writePermissionTable
    rfl

end SP1Clean.Soundness
