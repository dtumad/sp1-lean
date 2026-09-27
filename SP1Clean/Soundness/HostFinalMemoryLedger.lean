import SP1Clean.Soundness.HostFinalMemoryView

/-! # Private Memory receipts in the physical host ledger

The old host components are silent on the three new boundary protocols. This is a static
property of registered circuits. Selecting the five boundary tables therefore preserves
these ledgers exactly, while their Byte guarantees still come from the full assembly.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The only protocols introduced by complete outgoing Memory validation. -/
def privateChannels : List (RawChannel (ZMod p)) :=
  [(FinalMemoryValue.channel false).toRaw, (FinalMemoryValue.channel true).toRaw,
   FinalMemoryChange.channel.toRaw]

/-- Installed handlers/resources keep the final-memory receipt protocols private. -/
def PrivateInterface (others : List (HostLocalHandoff.Receiver (p := p)))
    (resources : List (Component (ZMod p))) : Prop :=
  ∀ channel ∈ privateChannels (p := p), ∀ component ∈ others.map (·.component) ++ resources,
    channel ∉ component.circuit.channels

omit [Fact (2 ^ 25 < p)] in
private theorem silent_of_names (component : Component (ZMod p)) (channel : RawChannel (ZMod p))
    (quiet : (component.circuit.channels.map RawChannel.name).contains channel.name = false) :
    channel ∉ component.circuit.channels := by
  intro member
  have used := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  rw [quiet] at used
  contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

private theorem private_not_local (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    channel ∉ (LocalCore.ensemble (p := p) image source).channels := by
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl <;>
    intro member <;>
    have names := List.mem_map_of_mem (f := RawChannel.name) member <;>
    simp [LocalCore.ensemble, sp1Ensemble_channels, OrderedBoundary.channel,
      SnapshotMemoryEnsemble.channelName, OrderedFinalProvider.channelName,
      FinalMemoryValue.channel, FinalMemoryChange.channel,
      stateChannel, memoryChannel, byteChannel, programChannel, exitChannel, syscallChannel,
      publicValuesChannel, Channel.toRaw] at names

private def fixedAdditions (image : ProgramImage) : List (Component (ZMod p)) :=
  [⟨ProtectedStore.byte⟩, ⟨ProtectedStore.half⟩, ⟨ProtectedStore.word⟩, ⟨ProtectedStore.double⟩,
   ⟨WritePermissionProvider.circuit image⟩, HostCallLedger.producer,
   HostHintReadHandoff.receiver.component] ++ HostHintReadHandoff.wordResources

private theorem additions_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p))
    (component : Component (ZMod p)) (member : component ∈ fixedAdditions (p := p) image) :
    channel ∉ component.circuit.channels := by
  apply silent_of_names
  have quiet : (fixedAdditions (p := p) image).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true := by
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
    rcases privateChannel with rfl | rfl | rfl <;> rfl
  simpa using List.all_eq_true.mp quiet component member

/-- Receipt freshness follows from the existing core inventory and the installed resource interface. -/
theorem beforeChecks_private (interface : PrivateInterface others resources)
    (channel : RawChannel (ZMod p)) (privateChannel : channel ∈ privateChannels (p := p)) :
    ∀ component ∈ beforeChecks image source others resources, channel ∉ component.circuit.channels := by
  intro component member
  change component ∈ (ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer ++ _ at member
  rcases List.mem_append.mp member with core | auxiliary
  · rcases List.mem_or_eq_of_mem_set core with retained | rfl
    · rcases List.mem_append.mp retained with stores | permission
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
          · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
            · rcases List.mem_or_eq_of_mem_set stores with old | rfl
              · exact fun used => private_not_local channel privateChannel
                  (LocalCore.component_channels_subset image source component
                    (List.mem_cons_of_mem _ old) used)
              · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
            · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
          · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
        · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
      · obtain rfl := List.mem_singleton.mp permission
        exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
    · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
  · change component ∈ (HostHintReadHandoff.receiver :: others).map (·.component) ++
        (HostHintReadHandoff.wordResources ++ resources) at auxiliary
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at auxiliary
    rcases auxiliary with rfl | other | word | resource
    · exact additions_private (image := image) channel privateChannel _ (by simp [fixedAdditions])
    · exact interface channel privateChannel component (List.mem_append_left _ other)
    · exact additions_private (image := image) channel privateChannel component (List.mem_append_right _ word)
    · exact interface channel privateChannel component (List.mem_append_right _ resource)

/-- The legacy padding restriction introduces no receipt-channel occurrence. -/
theorem padding_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    channel ∉ HaltPaddingChip.component.circuit.channels := by
  apply silent_of_names
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl <;> rfl

/-- The currently installed six-call registry and fixed hint/bank resources satisfy receipt privacy. -/
theorem source_privacy (hints : List Bytes) :
    PrivateInterface (HostCallReceivers.available (p := p)) (HostHintReadLocal.sourceResources hints) := by
  intro channel privateChannel component member
  apply silent_of_names
  have quiet : ((HostCallReceivers.available (p := p)).map
      (fun receiver : HostLocalHandoff.Receiver (p := p) => receiver.component) ++
      HostHintReadLocal.sourceResources hints).all
      (fun component => !(component.circuit.channels.map RawChannel.name).contains channel.name) = true := by
    simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
    rcases privateChannel with rfl | rfl | rfl <;> rfl
  simpa using List.all_eq_true.mp quiet component member

/-- Queue, bank and CPU verifier boundaries do not use the new Memory receipt protocols. -/
theorem base_verifier_private (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    channel ∉ (base image source target final bankFinal others resources channels).verifier.channels := by
  apply silent_of_names (component := ⟨(base image source target final bankFinal others resources channels).verifier⟩)
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl <;> rfl

end SP1Clean.Soundness.HostFinalMemory
