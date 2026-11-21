module

public import SP1Clean.FormalModel.Shard
public import SP1Clean.Math.SP1Field
public import SP1Clean.Semantics.Resources.HintAllocations

/-! # Persistent hint pointers for native admissible executions

The initial live hints and cumulative new nodes have independent ceilings. Their sum fits the
48-bit queue encoding in SP1's field, including at cuts where nodes have already been popped.
-/

@[expose] public section

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard HintQueue

/-- Every cut of a native eight-call execution has an encodable persistent cursor. Its immutable
nodes remain readable in the final inventory, with the same pointers, bytes and tails. -/
theorem admissibleExecution_hintInventory {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (cut : ℕ) :
    let hostPolicy := policy SP1Prime image
    ∃ reached cursor final,
      ExecutionPath hostPolicy image.program source.realize (events.take cut) reached ∧
      storeAfter? hostPolicy image.program source.realize (events.take cut) (ofList source.host.io.hints) = some cursor ∧
      Represents cursor.1 cursor.2 reached.host.io.hints ∧
      cursor.1.size = source.host.io.hints.length +
        executionResources hostPolicy image.program source.realize (events.take cut) .allocatedHints ∧
      cursor.2 ≤ cursor.1.size ∧ cursor.1.size < 2 ^ 48 ∧
      storeAfter? hostPolicy image.program reached (events.drop cut) cursor = some final ∧
      storeAfter? hostPolicy image.program source.realize events (ofList source.host.io.hints) = some final ∧
      Extends cursor.1 final.1 ∧ Represents final.1 final.2 target.host.io.hints := by
  obtain ⟨reached, cursor, final, path, built, rep, size, suffixBuilt, allBuilt, extension, finalRep⟩ :=
    storeAfter_at execution.1.2 cut
  refine ⟨reached, cursor, final, path, built, rep, size, rep.bound, ?_, suffixBuilt, allBuilt, extension, finalRep⟩
  have usage := execution.2.2.1
  have combined := path.resources_append (events.drop cut)
  rw [List.take_append_drop] at combined
  rw [combined] at usage
  have fresh := usage.left .allocatedHints
  have incoming := execution.2.2.2.1 .liveHints
  change source.host.io.hints.length ≤ SP1Prime - 1 at incoming
  change _ ≤ SP1Prime - 1 at fresh
  rw [size]
  exact (Nat.add_le_add incoming fresh).trans_lt (by decide)

end SP1Clean.TraceGen
