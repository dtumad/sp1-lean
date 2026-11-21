module

public import SP1Clean.FormalModel.Shard
public import SP1Clean.Math.SP1Field
public import SP1Clean.Semantics.Host.HintQueueWordRecords
public import SP1Clean.Semantics.Resources.HintAllocations

/-! # Persistent hint pointers for native admissible executions

The initial live hints and cumulative new nodes have independent ceilings. Their sum fits the
48-bit queue encoding in SP1's field, including at cuts where nodes have already been popped.
-/

@[expose] public section

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard HintQueue

/-- The canonical field records fit for all allocated nodes, including unreachable history.
Every padded word position appears in the generator and binds the original bytes in the final store. -/
def HintRecordsAt (current final : Store) : Prop :=
  ∀ pointer node, node? current pointer = some node →
    (NodeRecord.encode (p := SP1Prime) pointer node).Valid ∧
    (NodeRecord.encode (p := SP1Prime) pointer node).Binds final ∧
    node.bytes.length < 2 ^ 64 ∧
    ∀ index < wordCount node.bytes,
      let row := WordRecord.encode (p := SP1Prime) pointer node.bytes index
      row ∈ nodeWordRows pointer node.bytes ∧ row.Valid ∧ row.Binds final

private theorem hintRecordsAt_of_bounds {current final : Store}
    (valid : WellFormed current) (extension : Extends current final)
    (frontier : current.size < 2 ^ 48)
    (byteLimit : ∀ bytes ∈ current.toList.map Node.bytes, bytes.length ≤ SP1Prime - 1) :
    HintRecordsAt current final := by
  intro pointer node read
  have ⟨positive, inStore⟩ := node?_bound read
  have fits := inStore.trans_lt frontier
  have finalRead := extension pointer node read
  have member : node ∈ current.toList := by
    cases pointer with
    | zero => contradiction
    | succ index => exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? read)
  have bytes := byteLimit _ (List.mem_map_of_mem member)
  refine ⟨NodeRecord.encode_valid _ _ fits (valid _ _ read),
    NodeRecord.encode_binds finalRead fits (valid _ _ read), bytes.trans_lt (by decide), ?_⟩
  intro index position
  have indexFits : index < 2 ^ 48 := by
    unfold wordCount at position
    unfold SP1Prime at bytes
    omega
  exact ⟨nodeWordRows_complete _ _ _ position indexFits, WordRecord.encode_valid _ _ _ positive fits,
    WordRecord.encode_binds finalRead fits _ position indexFits⟩

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
      Extends cursor.1 final.1 ∧ Represents final.1 final.2 target.host.io.hints ∧
      HintRecordsAt cursor.1 final.1 := by
  obtain ⟨reached, cursor, final, path, built, valid, rep, size, suffixBuilt, allBuilt, extension, finalRep⟩ :=
    storeAfter_at execution.1.2 cut
  have usage := execution.2.2.1
  have combined := path.resources_append (events.drop cut)
  rw [List.take_append_drop] at combined
  rw [combined] at usage
  have fresh := usage.left .allocatedHints
  have incoming := execution.2.2.2.1 .liveHints
  change source.host.io.hints.length ≤ SP1Prime - 1 at incoming
  change _ ≤ SP1Prime - 1 at fresh
  have frontier : cursor.1.size < 2 ^ 48 := by
    rw [size]
    exact (Nat.add_le_add incoming fresh).trans_lt (by decide)
  refine ⟨reached, cursor, final, path, built, rep, size, rep.bound, frontier, suffixBuilt, allBuilt,
    extension, finalRep, hintRecordsAt_of_bounds valid extension frontier ?_⟩
  apply storeAfter_byte_bound path built _ (usage.left .liveHintBytes)
  intro bytes member
  rw [ofList_bytes, List.mem_reverse] at member
  exact (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) member)).trans
    (execution.2.2.2.1 .liveHintBytes)

end SP1Clean.TraceGen
