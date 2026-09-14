import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.HostLocalCoreMemory

/-! # Full Memory balance of the installed hint handlers

The source-backed queue assembly derives the complete Memory record permutation directly from
its actual AIR constraints and balance. The word consumers and wrapper accesses stay in that
ledger. This establishes conservation of complete records, not predecessor value currency.
-/

namespace SP1Clean.Soundness.HostHintReadLocal

open Circuit Air.Flat Channels Model.Core Semantics HostHintReadHandoff

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance memoryLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance memoryLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Every physical consumer's prior/new pair occurs in the full interior, with order and
duplicate occurrences preserved. The statement also retains the mandatory padding words. -/
theorem word_memory_sublist {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source others resources channels)) :
    ((TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)).flatMap (fun row =>
      [memoryChannel.pulledValue (HintReadCoverage.rowInput row).ram.prior,
       memoryChannel.pushedValue (HintReadCoverage.rowInput row).ram.pushed])).Sublist
      ((HostLocalCore.memoryInterior witness).map TypedInteraction.raw) := by
  rw [HostLocalCore.memoryInterior_raw, ← HintReadWriteLedger.memory_ledger _ (wordTables_aligned witness)]
  have suffix : (witness.tables.drop 60).Sublist (witness.tables.drop 6) := by
    simpa only [List.drop_drop] using List.drop_sublist 54 (witness.tables.drop 6)
  have physical : (wordTables witness).Sublist (witness.tables.drop 6) :=
    ((List.take_sublist 2 _).trans (List.drop_sublist _ _)).trans suffix
  exact physical.flatMap _

private theorem word_memoryBinary (last : Bool) :
    NativeCore.MemoryBinary (HintReadCoverage.view (p := p) last).component := by
  intro data physical _ interaction member
  rw [HintReadWriteLedger.row_memory_values (last, Environment.fromArray physical data)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact signedVal_binary_of_selector_gated (1 : ZMod p) _ (Or.inr rfl) (Or.inl rfl)
  · exact signedVal_binary_of_selector_gated (1 : ZMod p) _ (Or.inr rfl) (Or.inr (Or.inr rfl))

private theorem source_memoryBinary (source : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p)) :
    ∀ component ∈ (receiver :: HostCallReceivers.available).map (·.component) ++
      (wordResources ++ (sourceResources source.host.io.hints ++ [⟨(HostHintQueueBoundary.boundary source final).circuit⟩])),
      NativeCore.MemoryBinary component := by
  intro component member
  have split : component ∈ wordResources ∨ component ∈
      (receiver :: HostCallReceivers.available).map (·.component) ++
        (sourceResources source.host.io.hints ++ [⟨(HostHintQueueBoundary.boundary source final).circuit⟩]) := by
    simpa only [List.mem_append, or_assoc, or_left_comm, or_comm] using member
  rcases split with word | other
  · simp only [wordResources, List.mem_cons, List.not_mem_nil, or_false] at word
    rcases word with rfl | rfl <;> exact word_memoryBinary _
  · apply NativeCore.memoryBinary_of_silent
    have checked : ((receiver (p := p) :: HostCallReceivers.available).map
        (fun view : HostLocalHandoff.Receiver (p := p) => view.component) ++
        (sourceResources source.host.io.hints ++
          [(⟨(HostHintQueueBoundary.boundary source final).circuit⟩ : Component (ZMod p))])).all
        (fun component => !(component.circuit.channels.map RawChannel.name).contains
          (memoryChannel (p := p)).toRaw.name) = true := rfl
    intro used
    have silent := List.all_eq_true.mp checked component other
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at silent
    contradiction

variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
  {channels : List (RawChannel (ZMod p))}

/-- The installed source/queue/word assembly closes the complete Memory record permutation.
There is no Memory guarantee, host-currentness, or multiplicity premise from the caller. -/
theorem source_memory_records_perm
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records
      (LocalCore.sourceWitness (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) ++
      producedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))).Perm
    (FinalMemoryEnsemble.records
      (LocalCore.finalWitness (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) ++
      consumedMessages (HostLocalCore.memoryInterior (HostHintQueueBoundary.expanded witness))) :=
  HostLocalCore.memory_records_perm (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced) (source_memoryBinary source final)

end SP1Clean.Soundness.HostHintReadLocal
