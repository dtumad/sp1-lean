import SP1Clean.Proofs.Completeness.HintInventory
import SP1Clean.Semantics.Host.HintQueueSnapshot

/-! # Reading the outgoing queue of an arbitrary native shard -/

namespace SP1Clean.TraceGen

open Semantics Machine FormalModel.Shard HintQueue

/-- Replay constructs the final private head, allocation frontier and the exact target walk.
This includes fresh nodes that remain visible after intervening allocations and pops. -/
theorem admissibleExecution_hintSnapshot {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    ∃ cursor tails,
      storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some cursor ∧
      cursor.1.size = source.host.io.hints.length +
        executionResources (policy SP1Prime image) image.program source.realize events .allocatedHints ∧
      ReadsSnapshot SP1Prime cursor.1 cursor.2 target.host.io.hints tails := by
  obtain ⟨_, cursor, _, _, built, _, frontier, _, fits, _, completed, _, reached, _⟩ :=
    admissibleExecution_hintInventory execution events.length
  simp only [List.take_length] at built frontier
  obtain rfl := Option.some.inj (built.symm.trans completed)
  obtain ⟨tails, valid⟩ := reached.readsSnapshot (p := SP1Prime) fits (by
    intro bytes member
    have live := execution.2.2.2.2.1 .liveHintBytes
    change (target.host.io.hints.map List.length).sum ≤ SP1Prime - 1 at live
    have charged := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) member)
    unfold wordCount SP1Prime at *
    omega)
  exact ⟨cursor, tails, built, frontier, valid⟩

end SP1Clean.TraceGen
