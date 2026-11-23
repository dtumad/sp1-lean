import SP1Clean.Soundness.HostLocalCoreRows
import SP1Clean.Soundness.LocalCoreTouches

/-! # Low-clock bounds from the full host Memory ledger

Original instruction and refresh pushes use constraints, Byte guarantees, and Program balance.
Auxiliary pushes remain in the physical ledger and supply their own local clock bounds. Full record conservation then transfers
these bounds to predecessors; no instruction-only Memory balance is asserted.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}
    {channelNames : ((registry image source channels).map (·.name)).Nodup}
    {tableChannels : ∀ component ∈ auxiliary, component.circuit.channels ⊆ registry image source channels}

/-- Every physical interior push has a bounded low clock. The exact Memory decomposition
retains the instruction ledger and all auxiliary pushes; Memory balance is not assumed. -/
theorem memoryInterior_push_bound (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels names channelNames tableChannels))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees byteChannel.toRaw)
    (program : (localWitness witness).BalancedChannel programChannel.toRaw)
    (extra : ∀ table ∈ auxiliaryTables witness,
      ∀ message ∈ producedMessages (typedTableInteractionsWith table memoryChannel),
        MemoryMsg.ClkBound message) :
    ∀ message ∈ producedMessages (memoryInterior witness), MemoryMsg.ClkBound message := by
  have originalBytes := localWitness_byte_of_guarantees witness bytes
  have original := LocalCore.memoryInterior_push_bound valid (localWitness witness)
    (localWitness_constraints witness constraints) originalBytes program
  intro message member
  rw [memoryInterior_eq, producedMessages_append, List.mem_append] at member
  rcases member with old | auxiliary
  · exact original message old
  · rw [auxiliaryMemory, producedMessages_flatMap] at auxiliary
    obtain ⟨table, tableMem, emitted⟩ := List.mem_flatMap.mp auxiliary
    exact extra table tableMem message emitted

end SP1Clean.Soundness.HostLocalCore
