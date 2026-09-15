import SP1Clean.Soundness.HostQueueCPUOrder
import SP1Clean.Soundness.HostHintReadLocalMemory

/-! # Physical hint RAM accesses grouped by their actual CPU events

Cursor balance gives every word a handler, and full HostCall balance identifies its active
instruction. Distinct CPU clocks make grouping exhaustive without losing duplicate physical
occurrences. These are the access lists for mixed Memory grounding; predecessor value truth
and complete outgoing-state agreement remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def wordTime (row : HintReadCoverage.Row (p := p)) : ℕ :=
  clkNat (HintReadCoverage.rowInput row).ram.clk_high (HintReadCoverage.rowInput row).ram.clockLow

def wordClock (row : HintReadCoverage.Row (p := p)) : ZMod p × ZMod p :=
  HostHintReadPartition.clock (HintReadCoverage.rowInput row).previous

noncomputable def cpuClock (data : ProverData (ZMod p)) (event : ExecutionRow p) : ZMod p × ZMod p :=
  ((event.edge data).1.clk_high, (event.edge data).1.clk_low)

/-- The physical words selected by one decoded CPU event, in their retained table order. -/
noncomputable def wordsAt (data : ProverData (ZMod p)) (words : List (HintReadCoverage.Row (p := p)))
    (event : ExecutionRow p) : List (HintReadCoverage.Row (p := p)) :=
  words.filter (fun row => decide (wordClock row = cpuClock data event))

def touch (row : HintReadCoverage.Row (p := p)) : TimedGrounding.Touch p :=
  (((HintReadCoverage.rowInput row).ram.prior, wordTime row), (HintReadCoverage.rowInput row).ram.pushed)

private theorem wrapper_clock (data : ProverData (ZMod p)) (input : HostCallChip.Inputs (ZMod p))
    (flag : ZMod p) : cpuClock data (.syscall input.instruction) =
      ((input.message flag).clk_high, (input.message flag).clk_low) := rfl

private theorem wrapper_call_clock (data : ProverData (ZMod p)) (env : Environment (ZMod p)) :
    cpuClock data (.syscall (HostCallLedger.input env).instruction) =
      ((HostCallLedger.call env).clk_high, (HostCallLedger.call env).clk_low) :=
  wrapper_clock data (HostCallLedger.input env) _

omit [Fact (2 ^ 25 < p)] in
private theorem handler_clock (env : Environment (ZMod p)) :
    HostHintReadPartition.callClock env =
      ((HostHintReadCoverage.input env).call.clk_high, (HostHintReadCoverage.input env).call.clk_low) := by
  simp only [HostHintReadPartition.callClock, HostHintReadPartition.clock, HostHintReadChip.Inputs.first]

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem queue_read_call (env : Environment (ZMod p)) :
    HostQueueCPUOrder.call (none, env) = (HostHintReadCoverage.input env).call := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem word_clock_time (row : HintReadCoverage.Row (p := p)) :
    clkNat (wordClock row).1 (wordClock row).2 = wordTime row := by
  simp only [wordClock, HostHintReadPartition.clock, HintReadWordChip.Inputs.previous, wordTime]

private theorem cpu_clock_time (data : ProverData (ZMod p)) (event : ExecutionRow p) :
    clkNat (cpuClock data event).1 (cpuClock data event).2 = StateMsg.timeNat (event.edge data).1 := rfl

private theorem clock_keys_nodup (data : ProverData (ZMod p)) (cpu events : List (ExecutionRow p))
    (exhaustive : cpu.Perm events)
    (unique : (events.map (fun event => StateMsg.timeNat (event.edge data).1)).Nodup) :
    (cpu.map (cpuClock data)).Nodup := by
  have perm : (cpu.map (fun event => StateMsg.timeNat (event.edge data).1)).Perm
      (events.map (fun event => StateMsg.timeNat (event.edge data).1)) := exhaustive.map _
  have ordered : (cpu.map (fun event => StateMsg.timeNat (event.edge data).1)).Nodup := perm.nodup_iff.mpr unique
  have mapped : ((cpu.map (cpuClock data)).map (fun key => clkNat key.1 key.2)).Nodup := by
    simpa only [List.map_map, Function.comp_def, cpu_clock_time] using ordered
  exact List.Nodup.of_map _ mapped

private theorem local_data {auxiliary : List (Component (ZMod p))}
    {image : ProgramImage} {source : ExecutionSnapshot} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (HostLocalCore.ensemble image source auxiliary channels)) :
    (HostLocalCore.localWitness witness).data = witness.data := rfl

private theorem touch_at (data : ProverData (ZMod p)) (event : ExecutionRow p)
    (row : HintReadCoverage.Row (p := p))
    (facts : HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (same : wordClock row = cpuClock data event) :
    TimedGrounding.TouchOK (StateMsg.timeNat (event.edge data).1) (touch row).1 (touch row).2 := by
  have time := congrArg (fun key : ZMod p × ZMod p => clkNat key.1 key.2) same
  rw [word_clock_time, cpu_clock_time] at time
  rw [← time]
  exact facts.touch

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

private theorem handler_queue_member
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment) :
    (none, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices (queueTables witness) := by
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp member
  simp only [TransitionView.readIndexedRows, HostQueueOrder.indices, queueTables,
    List.zip_cons_cons, List.flatMap_cons]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨physical, physicalMem, rfl⟩)

/-- Every physical word belongs to an actual active syscall with the handler's complete call.
The clock is derived from the two installed ledgers, independently of Memory-value guarantees. -/
theorem word_cpu
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (steps : HintReadCoverage.Steps (wordTables witness))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) :
    ∃ handler ∈ (handlerTable witness).table.map (handlerTable witness).environment,
      ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable witness),
        HostCallLedger.call env = (HostHintReadCoverage.input handler).call ∧
        ExecutionRow.syscall (HostCallLedger.input env).instruction ∈
          LocalCore.executionRows (HostLocalCore.localWitness witness) ∧
        cpuClock witness.data (.syscall (HostCallLedger.input env).instruction) = wordClock row := by
  obtain ⟨handler, handlerMem, same⟩ := consumer_has_handler witness interface balanced steps row member
  obtain ⟨env, active, call, physical, _⟩ := HostQueueCPUOrder.call_cpu witness interface constraints balanced
    (none, handler) (handler_queue_member witness handler handlerMem)
  rw [queue_read_call] at call
  refine ⟨handler, handlerMem, env, active, call, physical, ?_⟩
  rw [handler_clock] at same
  exact (wrapper_call_clock witness.data env).trans
    ((congrArg (fun message : HostCallChip.Message (ZMod p) => (message.clk_high, message.clk_low)) call).trans same)

/-- An actual handler's physical words are exactly its authenticated node's padded write
inventory. This does not require the current call or its preceding CPU replay to succeed. -/
theorem handler_writes
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (store : HintQueue.Store) (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (env : Environment (ZMod p))
    (member : env ∈ (handlerTable witness).table.map (handlerTable witness).environment) :
    ∃ node, HintQueue.node? store (Address.toNat (HostHintReadCoverage.input env).node.pointer) = some node ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) (wordTables witness))).map
          HintReadWrites.produced).Perm
        (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) node.bytes) := by
  have valid : HostHintReadCoverage.handler.Spec env := by
    obtain ⟨physical, present, same⟩ := List.mem_map.mp member
    have checked := handler_spec witness interface store authenticated constraints balanced physical present
    rwa [handlerTable_component, same] at checked
  have records := HostQueueHistory.records_of_witness witness store authenticated balanced
    (none, env) (handler_queue_member witness env member)
  have steps := word_steps witness interface store authenticated constraints balanced
  apply HostHintReadWrites.writes_of_records env _ valid
    (TransitionView.selectTables_aligned _ _ (fun last => (HintReadCoverage.view last).component)
      (HostHintReadPartition.keepWord _) (wordTables_aligned witness))
    (steps.select (HostHintReadPartition.keepWord _))
    (balanced_for witness interface constraints balanced env member) store records.1 records.2
  intro row present
  rw [TransitionView.readIndexedRows_selectTables] at present
  exact consumer_word_binding witness store authenticated balanced row (List.mem_filter.mp present).1

private theorem wordsAt_tables (data : ProverData (ZMod p)) (tables : List (Table (ZMod p)))
    (event : ExecutionRow p) :
    wordsAt data (TransitionView.readIndexedRows HintReadCoverage.variants tables) event =
      TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (cpuClock data event) tables) := by
  rw [HostHintReadPartition.rows_for]
  rfl

/-- Full HostCall agreement identifies the actual CPU group's physical handler words. -/
theorem handler_wordsAt
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness witness))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable witness).table.map (handlerTable witness).environment)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env)) :
    wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) event =
      TransitionView.readIndexedRows HintReadCoverage.variants
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) (wordTables witness)) := by
  obtain ⟨physical, _, sameCall, sameEvent⟩ := HostQueueCPUOrder.call_cpu_at witness interface
    constraints balanced (none, env) (handler_queue_member witness env handler) event member clock
  have same := congrArg (fun message : HostCallChip.Message (ZMod p) =>
    (message.clk_high, message.clk_low)) sameCall
  rw [wordsAt_tables, sameEvent, wrapper_call_clock, same, queue_read_call, handler_clock]

/-- A CPU event's hint writes have distinct destinations. Immutable word authentication
excludes repeated addresses even though the final consumer retains its address in the cursor. -/
theorem wordsAt_addresses_nodup
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (store : HintQueue.Store) (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) :
    ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)) event).map (fun row => (HintReadWrites.produced row).1)).Nodup := by
  by_cases empty : wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)) event = []
  · simp only [empty, List.map_nil, List.nodup_nil]
  obtain ⟨row, present⟩ := List.exists_mem_of_ne_nil _ empty
  obtain ⟨physical, selected⟩ := List.mem_filter.mp present
  obtain ⟨handler, member, clock⟩ := consumer_has_handler witness interface balanced
    (word_steps witness interface store authenticated constraints balanced) row physical
  have same : HostHintReadPartition.callClock handler = cpuClock witness.data event :=
    clock.trans (of_decide_eq_true selected)
  obtain ⟨node, _, writes⟩ := handler_writes witness interface store authenticated constraints balanced handler member
  rw [same] at writes
  have distinct := (writes.map Prod.fst).nodup_iff.mpr
    (HintQueue.wordWrites_addresses_nodup (Address.toNat (HostHintReadCoverage.input handler).span.start) node.bytes)
  rw [wordsAt_tables]
  simpa only [List.map_map, Function.comp_def] using distinct

omit [Fact (2 ^ 25 < p)] in
private theorem word_address (input : HintReadWordChip.Inputs (ZMod p)) :
    Word.toNat (MemoryBoundary.address input.ram.pushed) = Address.toNat input.address := by
  simp [MemoryBoundary.address, HostRamAccessChip.Inputs.pushed, HintReadWordChip.Inputs.address,
    Word.toNat, Address.toNat]

omit [Fact (2 ^ 25 < p)] in
/-- The authenticated physical address is the canonical Memory location's bus address. -/
theorem address_loc (row : HintReadCoverage.Row (p := p))
    (facts : HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram) :
    (HintReadWrites.produced row).1 = (MemoryMsg.locOf (touch row).2).busAddress := by
  simp only [HintReadWrites.produced, touch]
  exact (word_address (HintReadCoverage.rowInput row)).symm.trans facts.canonical.2.2

/-- Distinct authenticated destinations are distinct canonical Memory locations in the
actual timed carrier, independently of predecessor value truth. -/
theorem wordsAt_locations_nodup
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (store : HintQueue.Store) (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) :
    ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)) event).map (fun row => MemoryMsg.locOf (touch row).2)).Nodup := by
  have distinct := wordsAt_addresses_nodup witness interface store authenticated constraints balanced event
  have same : ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)) event).map (fun row => (HintReadWrites.produced row).1)) =
      ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables witness)) event).map (fun row => (MemoryMsg.locOf (touch row).2).busAddress)) := by
    apply List.map_congr_left
    intro row member
    exact address_loc row (word_touches witness interface constraints balanced row (List.mem_filter.mp member).1)
  rw [same] at distinct
  apply List.Nodup.of_map MemLoc.busAddress
  simpa only [List.map_map, Function.comp_def] using distinct

variable {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}

/-- The installed source-backed assembly supplies the word-step contracts used for grouping. -/
theorem source_word_steps
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    HintReadCoverage.Steps (wordTables (HostHintQueueBoundary.expanded witness)) :=
  word_steps (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))
    (HintQueue.ofList source.host.io.hints).1 (HostHintQueueBoundary.source_authentication witness constraints)
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced)

omit [Fact (2 ^ 25 < p)] in
private theorem read_call_code [Fact (2 ^ 17 < p)]
    (wrapper : HostCallChip.Inputs (ZMod p)) (flag : ZMod p)
    (input : HostHintReadChip.Inputs (ZMod p))
    (same : wrapper.message flag = input.call) (spec : HostHintReadChip.Spec input) :
    (syscallEventOfRow wrapper.instruction).rawCode = SyscallKind.hintRead.code := by
  change Word.toBitVec64 (wrapper.message flag).code = _
  rw [same, spec.1, HostHintReadChip.codeWord, Target.toBitVec64_bitVecToWord]

private theorem wordsAt_nil_of_not_read
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (store : HintQueue.Store) (authenticated : RecordAuthentication witness store)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness witness))
    (notRead : ∀ row, event = .syscall row → (syscallEventOfRow row).rawCode ≠ SyscallKind.hintRead.code) :
    wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)) event = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row present
  obtain ⟨physical, selected⟩ := List.mem_filter.mp present
  obtain ⟨handler, handlerMem, env, _, sameCall, cpuMem, sameClock⟩ := word_cpu
    witness interface constraints balanced
    (word_steps witness interface store authenticated constraints balanced) row physical
  have time := congrArg (fun key : ZMod p × ZMod p => clkNat key.1 key.2)
    (sameClock.trans (of_decide_eq_true selected))
  rw [cpu_clock_time, cpu_clock_time] at time
  have unique := LocalCore.executionRows_times_nodup_of_orderingChannels
    (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints _ constraints)
    (HostLocalCore.orderingChannels _ (auxiliaryInterface interface) constraints balanced)
  rw [local_data] at unique
  have sameEvent := List.inj_on_of_nodup_map unique member cpuMem time.symm
  have spec : HostHintReadChip.Spec (HostHintReadCoverage.input handler) := by
    obtain ⟨physical, physicalMem, same⟩ := List.mem_map.mp handlerMem
    have checked := handler_spec witness interface _
      authenticated constraints balanced physical physicalMem
    rwa [handlerTable_component, same] at checked
  exact notRead _ sameEvent (read_call_code (HostCallLedger.input env) _ _ sameCall spec)

/-- Only an authenticated HINT_READ can own added hint RAM rows. CPU clock uniqueness rules
out assigning another call's words to a non-read event, without using Memory-value guarantees. -/
theorem source_wordsAt_nil_of_not_read
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (notRead : ∀ row, event = .syscall row → (syscallEventOfRow row).rawCode ≠ SyscallKind.hintRead.code) :
    wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))) event = [] := by
  exact wordsAt_nil_of_not_read (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints)) _
    (HostHintQueueBoundary.source_authentication witness constraints)
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced) event member notRead

/-- Every physical word occurs exactly once among the groups of any exhaustive CPU order.
This is an occurrence-preserving permutation, so grouping cannot erase duplicate accesses. -/
theorem words_partition
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (steps : HintReadCoverage.Steps (wordTables witness))
    (cpu : List (ExecutionRow p))
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness))) :
    (cpu.flatMap (wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables witness)))).Perm
      (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) := by
  have unique := LocalCore.executionRows_times_nodup_of_orderingChannels (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints)
    (HostLocalCore.orderingChannels witness (auxiliaryInterface interface) constraints balanced)
  rw [local_data] at unique
  have uniqueKeys := clock_keys_nodup witness.data cpu _ exhaustive unique
  have partition := List.flatMap_filter_key_perm
    (cpu.map (cpuClock witness.data))
    (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables witness)) wordClock uniqueKeys (by
      intro row member
      obtain ⟨_, _, env, _, _, physical, time⟩ := word_cpu witness interface constraints balanced steps row member
      exact List.mem_map.mpr ⟨.syscall (HostCallLedger.input env).instruction,
        exhaustive.mem_iff.mpr physical, time⟩)
  unfold wordsAt
  simpa only [List.flatMap_map, Function.comp_def] using partition

/-- The source-backed assembly derives every premise of the exact CPU word partition. -/
theorem source_words_partition
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (cpu : List (ExecutionRow p))
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))) :
    (cpu.flatMap (wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))))).Perm
      (TransitionView.readIndexedRows HintReadCoverage.variants (wordTables (HostHintQueueBoundary.expanded witness))) :=
  words_partition (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced)
    (source_word_steps witness constraints balanced) cpu exhaustive

/-- Grouping by CPU events preserves the complete raw Memory ledger of both word tables. -/
theorem source_memory_partition
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (cpu : List (ExecutionRow p))
    (exhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))) :
    (cpu.flatMap (fun event =>
      (wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event).flatMap (fun row =>
          [memoryChannel.pulledValue (touch row).1.1, memoryChannel.pushedValue (touch row).2]))).Perm
      ((wordTables (HostHintQueueBoundary.expanded witness)).flatMap (·.interactionsWith memoryChannel.toRaw)) := by
  rw [HintReadWriteLedger.memory_ledger _ (wordTables_aligned (HostHintQueueBoundary.expanded witness))]
  have perm := (source_words_partition witness constraints balanced cpu exhaustive).flatMap_right
    (fun row => [memoryChannel.pulledValue (touch row).1.1, memoryChannel.pushedValue (touch row).2])
  simpa only [List.flatMap_assoc, touch] using perm

/-- The installed source assembly supplies location uniqueness for every CPU group. -/
theorem source_locations_nodup
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) :
    ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))) event).map
        (fun row => MemoryMsg.locOf (touch row).2)).Nodup :=
  wordsAt_locations_nodup (HostHintQueueBoundary.expanded witness)
    (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))
    (HintQueue.ofList source.host.io.hints).1 (HostHintQueueBoundary.source_authentication witness constraints)
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced) event

omit [Fact (2 ^ 25 < p)] in
private theorem touches_chain (rows : List (HintReadCoverage.Row (p := p)))
    (unique : (rows.map (fun row => MemoryMsg.locOf (touch row).2)).Nodup) (loc : MemLoc) :
    List.IsChain (fun a b : TimedGrounding.Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      ((rows.map touch).filter (fun access => MemoryMsg.locOf access.2 = loc)) := by
  have mapped : ((rows.map touch).map (fun access => MemoryMsg.locOf access.2)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using unique
  have bound := pairwise_distinct_filter_length_le_one (fun access : TimedGrounding.Touch p => MemoryMsg.locOf access.2)
    (rows.map touch) loc (List.pairwise_map.mp mapped)
  generalize (rows.map touch).filter (fun access => MemoryMsg.locOf access.2 = loc) = selected at bound ⊢
  rcases selected with _ | ⟨_, _ | ⟨_, _⟩⟩
  · exact .nil
  · exact .singleton _
  · simp only [List.length_cons] at bound
    omega

/-- The host part of each CPU row satisfies the grounding engine's per-location chain law.
All its writes share the event's access time, and authenticated coverage makes locations unique. -/
theorem source_touches_chain
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) (loc : MemLoc) :
    List.IsChain (fun a b : TimedGrounding.Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.expanded witness))) event).map touch).filter
          (fun access => MemoryMsg.locOf access.2 = loc)) :=
  touches_chain _ (source_locations_nodup witness constraints balanced event) loc

/-- CPU grouping retains the previously derived aligned timing, pushed bounds, and strict
predecessor order of every physical hint word. -/
theorem source_touches_at (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p) :
    ∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.expanded witness))) event,
      TimedGrounding.TouchOK (StateMsg.timeNat (event.edge witness.data).1) (touch row).1 (touch row).2 ∧
      MemoryMsg.ClkBound (touch row).2 ∧ MemoryMsg.timeNat (touch row).1.1 < MemoryMsg.timeNat (touch row).2 := by
  intro row member
  obtain ⟨physical, clock⟩ := List.mem_filter.mp member
  have facts := source_word_touches witness constraints balanced row physical
  refine ⟨?_, facts.pushLow, source_word_order valid witness constraints balanced row physical⟩
  exact touch_at witness.data event row facts (of_decide_eq_true clock)

end SP1Clean.Soundness.HostHintReadCPU
