import SP1Clean.Soundness.HostHintQueueBoundary
import SP1Clean.Soundness.HostLocalCoreMemory
import SP1Clean.Soundness.HostRamTouches

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

private theorem word_access (last : Bool) (input : Var HintReadWordChip.Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((HintReadWordChip.main last input).operations offset).ConstraintsHold env)
    (bytes : ((HintReadWordChip.main last input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    HostRamTouches.AccessFacts (eval env input).ram := by
  have retained : ⟨offset, HostRamAccessChip.circuit.toSubcircuit offset input.ram⟩ ∈
      ((HintReadWordChip.main last input).operations offset).subcircuits := by
    simp only [HintReadWordChip.main, circuit_norm, Operations.subcircuits]
  have checked := constraintsHold_generalSubcircuit_of_mem env _ HostRamAccessChip.circuit
    input.ram offset retained constraints
  have guarantees := (channelGuarantees_toSubcircuit_generalFormalCircuit byteChannel.toRaw env
    HostRamAccessChip.circuit offset input.ram).mp
      (channelGuarantees_subcircuit_of_mem byteChannel.toRaw env _ _ retained bytes)
  have facts := HostRamTouches.of_constraints input.ram offset env checked guarantees
  have evaluated : eval env input.ram = (eval env input).ram := by
    rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
    rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
    simp only [circuit_norm]
  rwa [evaluated] at facts

/-- Every physical HINT_READ word contributes a bounded RAM touch at its call clock.
The actual AIR and Byte balance suffice; prior Memory guarantees and record authentication
are not premises of this structural step. -/
theorem word_touches {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness),
      HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram := by
  intro row member
  obtain ⟨⟨last, table⟩, paired, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  have component := List.forall₂_zip (wordTables_aligned witness) paired
  have present := wordTables_mem witness table (List.of_mem_zip paired).2
  have checked := constraints table present physical physicalMem
  have bytes := byte_guarantees witness interface constraints balanced table present physical physicalMem
  rw [← component] at checked bytes
  rw [Component.constraintsHold_iff] at checked
  rw [Component.channelGuarantees_iff] at bytes
  simp only [HintReadCoverage.view, Component.rowOperations, HintReadWordChip.circuit] at checked bytes
  have facts := word_access last (varFromOffset HintReadWordChip.Inputs 0)
    (size HintReadWordChip.Inputs) (table.environment physical) checked bytes
  simpa only [eval_varFromOffset_valueFromOffset, HintReadCoverage.rowInput] using facts

omit [Fact (2 ^ 25 < p)] in
private theorem touch_at_clock (input : HintReadWordChip.Inputs (ZMod p))
    (facts : HostRamTouches.AccessFacts input.ram) (key : ZMod p × ZMod p)
    (same : HostHintReadPartition.clock input.previous = key) :
    TimedGrounding.TouchOK (clkNat key.1 key.2) (input.ram.prior, clkNat key.1 key.2) input.ram.pushed := by
  have time := congrArg (fun clock : ZMod p × ZMod p => clkNat clock.1 clock.2) same
  change clkNat input.ram.clk_high input.ram.clockLow = clkNat key.1 key.2 at time
  simpa only [time] using facts.touch

/-- Filtering the physical word tables by a handler clock puts every retained touch in that
same execution window, including the final padding word. -/
theorem call_word_touches {image : ProgramImage} {source : ExecutionSnapshot}
    {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
    {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source others resources channels))
    (interface : ExtensionInterface others resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (key : ZMod p × ZMod p) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (HostHintReadPartition.tablesFor key (wordTables witness)),
      TimedGrounding.TouchOK (clkNat key.1 key.2)
        ((HintReadCoverage.rowInput row).ram.prior, clkNat key.1 key.2)
        (HintReadCoverage.rowInput row).ram.pushed := by
  intro row member
  rw [HostHintReadPartition.rows_for] at member
  obtain ⟨present, clock⟩ := List.mem_filter.mp member
  have facts := word_touches witness interface constraints balanced row present
  exact touch_at_clock _ facts key (of_decide_eq_true clock)

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

/-- The installed source/queue assembly closes the host word access facts without a caller
supplying a channel interface or any Memory guarantee. -/
theorem source_word_touches
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness)),
      HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram :=
  word_touches (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced)

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
