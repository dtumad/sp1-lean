module

public import SP1Clean.Proofs.Completeness.HintInventory
public import SP1Clean.Semantics.Resources.HistoricalHintWords

/-! # Capacity of historical hint records at every execution cut

The immutable store includes incoming buffers, direct WRITE allocations and ordered hook
replies. Its live portion is paid for by the current boundary. HINT_READ's cumulative RAM
writes pay for the padded words of every popped node. The bounds use the existing resource
profile and apply to the same authenticated store and suffix as the persistent inventory.
-/

@[expose] public section

namespace SP1Clean.TraceGen
open Semantics Machine HintQueue FormalModel.Shard

private theorem endpoint_fits {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} {limits : ResourceLimits}
    (path : ExecutionPath policy program source events target) (incoming : source.resources.Fits limits)
    (usage : (executionResources policy program source events).Fits limits) : target.resources.Fits limits := by
  induction path with
  | nil => exact incoming
  | cons step _ ih =>
    rw [executionResources_cons step] at usage
    exact ih usage.right.left usage.right.right

private theorem padded_byte_bounds (hints : List Bytes) :
    (hints.map List.length).sum ≤ 8 * (hints.map wordCount).sum ∧
      8 * (hints.map wordCount).sum ≤ (hints.map bytePayloadCost).sum := by
  induction hints with
  | nil => simp
  | cons bytes rest ih =>
    simp only [List.map_cons, List.sum_cons, wordCount, bytePayloadCost] at *
    omega

/-- Under any numeric preset, all historical raw bytes and all mandatory padded words fit
within the sum of the live boundary-payload allowance and the cumulative RAM write allowance.
This applies to the actual store produced by the mixed replay, including at an empty cut. -/
theorem historical_hint_budget {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} {limits : ResourceLimits} {cursor : Store × ℕ}
    (path : ExecutionPath policy program source events target)
    (built : storeAfter? policy program source events (ofList source.host.io.hints) = some cursor)
    (incoming : source.resources.Fits limits) (usage : (executionResources policy program source events).Fits limits) :
    storedByteCount cursor.1 ≤ 8 * storedWordCount cursor.1 ∧
      8 * storedWordCount cursor.1 + 125 ≤ limits.boundaryBytes + limits.writeBytes := by
  have boundary := endpoint_fits path incoming usage .boundaryBytes
  change target.resources .boundaryBytes ≤ limits.boundaryBytes at boundary
  have writes := usage .writeBytes
  change executionResources policy program source events .writeBytes ≤ limits.writeBytes at writes
  have live := (padded_byte_bounds target.host.io.hints).2
  have overhead : (target.host.io.hints.map bytePayloadCost).sum + 125 ≤ target.resources .boundaryBytes := by
    simp only [ExecutionState.resources, ExecutionState.boundaryPayload, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
    omega
  exact ⟨(padded_byte_bounds (cursor.1.toList.map Node.bytes)).1, by have := (storeAfter_totals path built).2; omega⟩

/-- The existing per-node generator realizes the full historical word count when its total
fits the 48-bit index space. This counts every original node at its own pointer. -/
theorem historical_wordRows_length {p : ℕ} [Fact p.Prime] (store : Store)
    (fits : storedWordCount store ≤ 2 ^ 48) :
    (List.ofFn fun i : Fin store.size => nodeWordRows (p := p) (i.val + 1) store[i.val].bytes).flatten.length =
      storedWordCount store := by
  have kept (i : Fin store.size) : min (wordCount store[i.val].bytes) (2 ^ 48) = wordCount store[i.val].bytes := by
    apply Nat.min_eq_left
    apply Nat.le_trans _ fits
    apply List.le_sum_of_mem
    apply List.mem_map_of_mem
    apply List.mem_map_of_mem
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  simp only [List.length_flatten, List.map_ofFn, Function.comp_def, nodeWordRows_length, kept]
  have allNodes : (List.ofFn fun i : Fin store.size => store[i.val]) = store.toList := by
    rw [← Array.toList_ofFn, Array.ofFn_getElem]
  have counts := congrArg (fun nodes : List Node => (nodes.map fun node => wordCount node.bytes).sum) allNodes
  simpa only [List.map_ofFn, Function.comp_def, storedWordCount, List.map_map] using counts

/-- At every cut of a native eight-call execution the same persistent store binds its full
history of node and word records in the final store. Each popped item contributes its actual
length to the raw-byte inventory and its paid RAM transfer to the padded word inventory.
All historical words, rounded once to a power of two, fit in at most 2^29 rows. -/
theorem admissibleExecution_historicalHintCapacity {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (cut : ℕ) :
    let hostPolicy := policy SP1Prime image
    let tape := events.take cut
    ∃ reached cursor final,
      ExecutionPath hostPolicy image.program source.realize tape reached ∧
      storeAfter? hostPolicy image.program source.realize tape (ofList source.host.io.hints) = some cursor ∧
      Represents cursor.1 cursor.2 reached.host.io.hints ∧
      storeAfter? hostPolicy image.program reached (events.drop cut) cursor = some final ∧
      storeAfter? hostPolicy image.program source.realize events (ofList source.host.io.hints) = some final ∧
      Extends cursor.1 final.1 ∧ HintRecordsAt cursor.1 final.1 ∧
      storedByteCount cursor.1 = (reached.host.io.hints.map List.length).sum + (tape.filterMap HintReadDemand.length?).sum ∧
      8 * storedWordCount cursor.1 = 8 * (reached.host.io.hints.map wordCount).sum +
        executionResources hostPolicy image.program source.realize tape .writeBytes ∧
      storedByteCount cursor.1 ≤ 8 * storedWordCount cursor.1 ∧
      8 * storedWordCount cursor.1 + 125 ≤ 2 * (SP1Prime - 1) ∧
      (List.ofFn fun i : Fin cursor.1.size =>
        nodeWordRows (p := SP1Prime) (i.val + 1) cursor.1[i.val].bytes).flatten.length = storedWordCount cursor.1 ∧
      2 ^ Nat.clog 2 (storedWordCount cursor.1) ≤ 2 ^ 29 := by
  obtain ⟨reached, cursor, final, path, built, represented, _, _, _, suffix, allBuilt, extension, _, records⟩ :=
    admissibleExecution_hintInventory execution cut
  have usage := execution.2.2.1
  have combined := path.resources_append (events.drop cut)
  rw [List.take_append_drop] at combined
  rw [combined] at usage
  have ⟨raw, paid⟩ := storeAfter_totals path built
  have ⟨unpadded, budget⟩ := historical_hint_budget path built execution.2.2.2.1 usage.left
  change 8 * storedWordCount cursor.1 + 125 ≤ (SP1Prime - 1) + (SP1Prime - 1) at budget
  have width : SP1Prime < 2 ^ 31 := by decide
  have rows : storedWordCount cursor.1 ≤ 2 ^ 29 := by omega
  exact ⟨reached, cursor, final, path, built, represented, suffix, allBuilt, extension, records, raw, paid, unpadded,
    by omega, historical_wordRows_length _ (rows.trans (by decide)), Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr rows)⟩

end SP1Clean.TraceGen
