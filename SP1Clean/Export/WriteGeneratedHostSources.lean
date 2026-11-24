import SP1Clean.Export.WriteHostSourceGrounding
import SP1Clean.Export.WriteRefreshTables
import SP1Clean.Proofs.Completeness.MixedMemorySyscall
import SP1Clean.Proofs.Completeness.MixedSyscallTable
import SP1Clean.Proofs.Completeness.WriteSourceCoverage

/-! # Original WRITE predecessors from the generated mixed instruction tables

Each semantic ECALL register access, HINT_READ word and register refresh identifies a positive
receipt in its actual physical producer. These are statements about the generated row arrays
at any evaluation data, as required when installing them in a common supervisor.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Soundness Machine Semantics TraceGen FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory

private abbrev F := ZMod SP1Prime

/-- The actual native receipt for the predecessor of a canonical mixed access. -/
def compiledReadback (base : ℕ) (access : MemoryHistoryAccess) : Readback F :=
  AccessSupply.atClock ((base / 2 ^ 24 : ℕ), (base % 2 ^ 24 : ℕ)) access.pulledEntry.toMemoryMsg

/-- A scheduled receipt covers every representable cut within its clipped predecessor
interval. Both fields of the requested value and address are the original encoded data. -/
theorem compiledReadback_covers {base cut : ℕ} {access : MemoryHistoryAccess}
    (legal : ValidKey access.loc.busAddress) (lower : access.previous ≤ cut) (upper : cut ≤ base) (fits : base < 2 ^ 48) :
    Counted.Covers (compiledReadback base access)
      ⟨Address.ofNat access.loc.busAddress, Address.ofNat cut, Target.bitVecToWord access.pulled⟩ := by
  simpa only [compiledReadback, MemoryHistoryAccess.pulledEntry, MemoryHistoryAccess.busAddress,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    Counted.covers_compiled_entry (p := SP1Prime) access.pulledEntry base cut legal lower upper fits

/-- Each scheduled ECALL register input from the mixed tape publishes the corresponding
positive full receipt in the compiled original instruction table. -/
theorem generated_ecall (compiled : List MixedCompiledRow) (frontier : AccessFrontier) (call : CoreSyscallEvent)
    (position : MixedCompiledRow.syscall frontier call.clock call ∈ compiled) (phase : activeClockPhase call.clock)
    {access : MemoryHistoryAccess} (used : access ∈ MixedMemoryHistory.instruction (.syscall frontier call.clock call))
    (data evaluation : ProverData F) (hint : ProverHint F) (fit) :
    ∃ cells ∈ (MixedSyscallTable.table compiled data hint fit).table,
      (1, compiledReadback call.clock access) ∈ rowRecords (.host .ecall) (Environment.fromArray cells evaluation) := by
  let row := syscallInstruction (p := SP1Prime) frontier call
  have input : row ∈ compiled.filterMap MixedCompiledRow.syscallInput? := List.mem_filterMap.mpr ⟨_, position, rfl⟩
  rw [← MixedSyscallTable.active compiled data evaluation hint fit] at input
  obtain ⟨env, envMem, received⟩ := List.mem_map.mp input
  obtain ⟨cells, present, rfl⟩ := List.mem_map.mp (List.mem_filter.mp envMem).1
  refine ⟨cells, present, ?_⟩
  have prior : access.pulledEntry.toMemoryMsg (p := SP1Prime) ∈ (syscallRowFacts row).memPulls.map Prod.fst := by
    rw [MixedMemoryHistory.syscall_pulls frontier call phase]
    exact List.mem_reverse.mpr (List.mem_map_of_mem used)
  obtain ⟨operand, read, message⟩ := List.mem_map.mp prior
  rw [ecall_records, received]
  apply List.mem_map.mpr
  refine ⟨operand, read, ?_⟩
  have incoming := (syscallInstruction_stateMessages (p := SP1Prime) frontier call).1
  change SyscallInstrsChip.statePulledMessage row = _ at incoming
  rw [incoming, message]
  rfl

/-- A selected HINT_READ word, including the final transfer of an empty or aligned hint,
supplies its original RAM predecessor from the correct continuing/final physical table. -/
theorem generated_hint {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {entry : Bool × HintReadWordChip.RowInput F} (used : entry ∈ HintReadTransfers.history image source events)
    (data evaluation : ProverData F) (fit) :
    let ram := entry.2.1.ram
    let original := HintReadTransfers.wordTable entry.1 (HintReadTransfers.history image source events) data fit
    ∃ cells ∈ original.table, (1, AccessSupply.atClock (ram.clk_high, ram.clockLow) ram.prior) ∈
      rowRecords (.host (.word entry.1)) (Environment.fromArray cells evaluation) := by
  intro ram original
  let c := HintReadCoverage.component (p := SP1Prime) entry.1
  let rows := HintReadTransfers.physicalInputs entry.1 (HintReadTransfers.history image source events)
  have occurs : entry.2 ∈ rows := List.mem_append_left _ (List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨used, by simp⟩, rfl⟩)
  let cells := c.buildRow entry.2 original.data (.empty _)
  have present : cells ∈ original.table := List.mem_map_of_mem occurs
  let env := Environment.fromArray cells evaluation
  have decoded : valueFromOffset HintReadWordChip.RowInput 0 env = entry.2 := c.rowInput_buildRow _ _ _ _
  have activity : HintReadCoverage.rowActivity (entry.1, env) = 1 := (HintReadTransfers.row_activity _ _).trans
    ((congrArg Prod.snd decoded).trans (HintReadTransfers.history_active run entry used))
  refine ⟨cells, present, ?_⟩
  change _ ∈ rowRecords (.host (.word entry.1)) env
  rw [word_records, activity]
  rw [show HintReadCoverage.rowInput (entry.1, env) = entry.2.1 from congrArg Prod.fst decoded]
  exact List.mem_singleton_self _

/-- Every generated register refresh contributes its original predecessor to the private
WRITE source directly from its own physical row. -/
theorem generated_refresh (registers : List MemoryBumpEvent) (states : List StateBumpEvent)
    {event : MemoryBumpEvent} (used : event ∈ registers)
    (data evaluation : ProverData F) (mh sh) :
    let original := (InstalledAssembly.bumpTables registers states data mh sh).1
    ∃ cells ∈ original.table, (1, InstalledAssembly.refreshEventReceipt event) ∈
      rowRecords .refresh (Environment.fromArray cells evaluation) := by
  intro original
  let c := providerTableFor (p := SP1Prime) .memoryBump
  let row := memoryBumpCols (p := SP1Prime) event
  let cells := c.buildRow row original.data (.empty _)
  have occurs : cells ∈ original.table := by
    rw [InstalledAssembly.bumpTables_registerRows]
    apply List.mem_map_of_mem (f := fun r => c.buildRow r original.data (.empty _))
    exact List.mem_append_left _ (List.mem_map_of_mem used)
  have decoded : valueFromOffset MemoryBumpChip.Inputs 0 (Environment.fromArray cells evaluation) = row :=
    c.rowInput_buildRow row original.data evaluation (.empty _)
  refine ⟨cells, occurs, ?_⟩
  change _ ∈ [((valueFromOffset MemoryBumpChip.Inputs 0 _).is_real, refreshReadback (valueFromOffset MemoryBumpChip.Inputs 0 _))]
  rw [decoded]
  exact List.mem_singleton_self _

end SP1Clean.Export.WriteSourceRegistry
