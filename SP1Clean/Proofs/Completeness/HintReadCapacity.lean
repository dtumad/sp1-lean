import SP1Clean.Soundness.HostHintReadCoverage
import SP1Clean.Semantics.Resources.HintReadDemand
import SP1Clean.FormalModel.ShardResources
import ToClean.Air.DemandPadding
import ToClean.Air.Footprint

/-! # HINT_READ physical channel capacity

The handler and both word consumers contribute their complete physical interaction lists,
before any cancellation. Demand padding retains those interactions even on inactive word rows.
-/

namespace SP1Clean.TraceGen.HintReadCapacity

open Soundness Air.Flat Circuit Channels Semantics Machine

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- All physical word-row channels in order, including guarded zero-weight occurrences. -/
theorem word_channels (last : Bool) :
    ((HintReadCoverage.component (p := p) last).operations.interactions.map (·.channel)) =
      List.replicate 6 byteChannel.toRaw ++ [memoryChannel.toRaw, memoryChannel.toRaw,
        HostRamAccessChip.channel.toRaw, HostHintQueue.wordChannel.toRaw] ++ List.replicate 6 byteChannel.toRaw ++
      [HostRamAccessChip.channel.toRaw] ++ List.replicate 8 WritePermissionProvider.channel.toRaw ++
      [HintReadWordChip.stateChannel.toRaw, HintReadWordChip.stateChannel.toRaw] := by
  rw [Component.interactions_eq]
  cases last <;> simp only [HintReadCoverage.component, Component.rowOperations, HintReadWordChip.circuit,
    Guarded.circuit, Guarded.main_interactions, HintReadWordChip.activeCircuit, HintReadWordChip.main,
    GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    HostRamAccessChip.circuit, HostRamAccessChip.main, HintReadStep.circuit, HintReadStep.main,
    AddrAddOperation.circuit, AddrAddOperation.main, AddressOperation.circuit, AddressOperation.main,
    Readers.MemoryAccess.circuit, Readers.MemoryAccess.main, WordRangeCheck.circuit, WordRangeCheck.main,
    Gadgets.Equality.circuit, Gadgets.Equality.main, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
    Gadgets.ToBits.rangeCheck, Gadgets.toBits, Gadgets.ToBits.main, List.ofFn_succ, List.ofFn_zero, circuit_norm]
  all_goals rfl

/-- Every occurrence contributed by the installed call handler. -/
theorem handler_channels :
    ((HostHintReadCoverage.handler (p := p)).operations.interactions.map (·.channel)) =
      List.replicate 6 byteChannel.toRaw ++ [HostHintQueue.wordChannel.toRaw] ++ List.replicate 6 byteChannel.toRaw ++
      [HostHintQueue.nodeChannel.toRaw, HostCallChip.channel.toRaw, HostHintQueue.stateChannel.toRaw,
       HostHintQueue.stateChannel.toRaw, HintReadWordChip.stateChannel.toRaw, HintReadWordChip.stateChannel.toRaw] := by
  rw [Component.interactions_eq]
  change (((Guarded.main HostHintReadChip.circuit inferInstance (varFromOffset HostHintReadChip.RowInput 0)).operations
    (size HostHintReadChip.RowInput)).interactions.map _) = _
  rw [Guarded.main_interactions]
  simp only [HostHintReadChip.circuit, HostHintReadChip.main,
    FormalCircuit.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions, HintReadSpan.circuit, HintReadSpan.main, HintReadStep.circuit,
    HintReadStep.main, ClockOrder.circuit, AddressDiv8.circuit, AddressOrder.circuit, AddrAddOperation.circuit,
    AddrAddOperation.main, WordRangeCheck.circuit, WordRangeCheck.main, Gadgets.Equality.circuit,
    Gadgets.Equality.main, List.map_cons, List.map_nil, List.nil_append, List.append_nil, Gadgets.ToBits.rangeCheck,
    Gadgets.toBits, Gadgets.ToBits.main, Gadgets.IsZeroField.circuit, ClockOrder.main, AddressOrder.main,
    AddressDiv8.main, List.ofFn_succ, List.ofFn_zero, circuit_norm]
  rfl

/-- Per-row occurrence widths in the installed circuits. The handler leaves every permission
request and RAM handoff to its word consumers. -/
theorem widths (last : Bool) :
    let word := HintReadCoverage.component (p := p) last
    let handler := HostHintReadCoverage.handler (p := p)
    word.channelWidth WritePermissionProvider.channel.toRaw = 8 ∧
    word.channelWidth HostRamAccessChip.channel.toRaw = 2 ∧ word.channelWidth memoryChannel.toRaw = 2 ∧
    word.channelWidth byteChannel.toRaw = 12 ∧ handler.channelWidth WritePermissionProvider.channel.toRaw = 0 ∧
    handler.channelWidth HostRamAccessChip.channel.toRaw = 0 ∧ handler.channelWidth memoryChannel.toRaw = 0 ∧
    handler.channelWidth byteChannel.toRaw = 12 := by
  classical
  have width (component : Component (ZMod p)) (channel : RawChannel (ZMod p)) :
      component.channelWidth channel = (component.operations.interactions.map (·.channel)).countP
        (fun item => decide (item = channel)) := by
    rw [List.countP_map, List.countP_eq_length_filter]
    rfl
  simp only [width, word_channels, handler_channels]
  simp [memoryChannel, byteChannel, HostRamAccessChip.channel, HostHintQueue.wordChannel,
    WritePermissionProvider.channel, HintReadWordChip.stateChannel, HostCallChip.channel,
    HostHintQueue.nodeChannel, HostHintQueue.stateChannel, Channel.toRaw]

/-- Exact counts on the original physical tables. Heights include every padding row. -/
theorem table_counts (handler next last : Table (ZMod p))
    (handlerType : handler.component = HostHintReadCoverage.handler)
    (nextType : next.component = HintReadCoverage.component false)
    (lastType : last.component = HintReadCoverage.component true) :
    let occurrences := fun channel => ([handler, next, last].flatMap (·.interactionsWith channel)).length
    let words := next.length + last.length
    occurrences WritePermissionProvider.channel.toRaw = 8 * words ∧
    occurrences HostRamAccessChip.channel.toRaw = 2 * words ∧
    occurrences memoryChannel.toRaw = 2 * words ∧
    occurrences byteChannel.toRaw = 12 * (words + handler.length) := by
  obtain ⟨np, nr, nm, nb, hp, hr, hm, hb⟩ := widths (p := p) false
  obtain ⟨lp, lr, lm, lb, _⟩ := widths (p := p) true
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    Table.interactionsWith_length, handlerType, nextType, lastType, np, nr, nm, nb, hp, hr, hm, hb, lp, lr, lm, lb]
  omega

/-- These three registered components all use Clean's demand padding, including height zero
when no rows were requested. -/
theorem targetHeight (state : WitnessGeneration.ComponentState (ZMod p))
    (installed : state.component = HostHintReadCoverage.handler ∨
        ∃ last, state.component = HintReadCoverage.component last) :
    state.targetHeight = WitnessGeneration.demandHeight state.rows.size := by
  cases state with
  | mk component multiplicity operations interactions rows messageRows =>
    rcases installed with eq | ⟨last, eq⟩ <;> change component = _ at eq <;> subst component <;>
      exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl

/-- Separately rounding the two word demands and the call demand preserves these bounds for
every real execution, even before any physical tables have been generated. -/
theorem demand_bounds {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    let lengths := events.filterMap HintReadDemand.length?
    let calls := WitnessGeneration.demandHeight lengths.length
    let words := WitnessGeneration.demandHeight (HintReadDemand.continuing lengths) + calls
    let paid := executionResources policy program source events .writeBytes
    4 * words ≤ paid ∧ 12 * (words + calls) ≤ 3 * paid + 24 * lengths.length ∧
      12 * (words + calls) ≤ 6 * paid := by
  dsimp only
  rw [HintReadDemand.writeBytes path]
  have hn := (WitnessGeneration.demandHeight_bounds (HintReadDemand.continuing (events.filterMap HintReadDemand.length?))).2
  have hf := (WitnessGeneration.demandHeight_bounds (events.filterMap HintReadDemand.length?).length).2
  omega

/-- With its semantic row demands padded separately, this HINT_READ block spends at most
twice the paid bytes on permission occurrences, half on each RAM ledger, and six times on the
shared Byte ledger. The tighter Byte bound retains the actual number of HINT_READ calls. -/
theorem padded_counts_le {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (execution : FormalModel.Shard.AdmissibleExecution limits p image source target events)
    (handler next last : Table (ZMod p))
    (handlerType : handler.component = HostHintReadCoverage.handler)
    (nextType : next.component = HintReadCoverage.component false)
    (lastType : last.component = HintReadCoverage.component true)
    (handlerHeight : handler.length = WitnessGeneration.demandHeight (events.filterMap HintReadDemand.length?).length)
    (nextHeight : next.length = WitnessGeneration.demandHeight (HintReadDemand.continuing (events.filterMap HintReadDemand.length?)))
    (lastHeight : last.length = handler.length) :
    let occurrences := fun channel => ([handler, next, last].flatMap (·.interactionsWith channel)).length
    occurrences WritePermissionProvider.channel.toRaw ≤ 2 * limits.writeBytes ∧
    2 * occurrences HostRamAccessChip.channel.toRaw ≤ limits.writeBytes ∧
    2 * occurrences memoryChannel.toRaw ≤ limits.writeBytes ∧
    occurrences byteChannel.toRaw ≤ 3 * limits.writeBytes + 24 * (events.filterMap HintReadDemand.length?).length ∧
    occurrences byteChannel.toRaw ≤ 6 * limits.writeBytes := by
  obtain ⟨permissions, ram, memory, bytes⟩ := table_counts handler next last handlerType nextType lastType
  have charge := execution.2.2.1 .writeBytes
  change executionResources _ _ _ _ .writeBytes ≤ limits.writeBytes at charge
  obtain ⟨wordBound, callBound, byteBound⟩ := demand_bounds execution.1.2
  dsimp only at permissions ram memory bytes ⊢
  rw [permissions, ram, memory, bytes]
  omega

end SP1Clean.TraceGen.HintReadCapacity
