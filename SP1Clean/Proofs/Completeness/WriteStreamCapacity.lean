import SP1Clean.Semantics.Host.WriteStreamRecords
import SP1Clean.FormalModel.ShardResources
import SP1Clean.Math.SP1Field

/-! # Fixed WRITE stream inventory under the actual native preset

Every output byte belongs to the outgoing snapshot. Every consumed hook reply, including all
returned hints, belongs to the incoming snapshot. The two existing endpoint byte budgets pay
for every metadata row and every index; no extra resource coefficient is an admitted premise.
-/

namespace SP1Clean.WriteEffects
open Semantics Machine FormalModel.Shard

/-- Length and data rows for the three outputs plus the existing source-side reply payload measurement. -/
def streamCost (s : WriteStreams) : Nat :=
  3 + s.stdout.length + s.stderr.length + s.publicOutput.length + (s.hooks.map HookReply.payloadCost).sum

private theorem count_indexed {α β : Type} (xs : List α) (rows : α × Nat → List β)
    (cost : α → Nat) (bound : ∀ x i, (rows (x,i)).length ≤ cost x) :
    (xs.zipIdx.flatMap rows).length ≤ (xs.map cost).sum := by
  rw [List.length_flatMap]
  have eq : (xs.zipIdx.map (fun x => cost x.1)).sum = (xs.map cost).sum := by
    change (xs.zipIdx.map (cost ∘ Prod.fst)).sum = _
    rw [← List.map_map, List.zipIdx_map_fst]
  rw [← eq]
  induction xs.zipIdx with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound y.1 y.2) ih

private theorem count_queries (s : WriteStreams) : (queries s).length ≤ streamCost s := by
  unfold queries streamCost
  simp only [List.length_append, byteQueries, List.length_cons, List.length_map, List.length_range]
  have each (reply : HookReply) (r : Nat) :
      ([Query.descriptor r, .returnCount r] ++ byteQueries (.request r) reply.request.input ++
        reply.hints.zipIdx.flatMap (fun (bytes, h) => byteQueries (.returned r h) bytes)).length ≤ reply.payloadCost := by
    have returned := count_indexed reply.hints (fun (b,h) => byteQueries (.returned r h) b) bytePayloadCost
      (by intro b h; simp [byteQueries, bytePayloadCost])
    simp only [List.length_append, byteQueries, List.length_cons, List.length_nil, List.length_map, List.length_range,
      HookReply.payloadCost, hintPayloadCost, bytePayloadCost] at *
    omega
  have total := count_indexed s.hooks (fun (reply, r) =>
    [Query.descriptor r, .returnCount r] ++ byteQueries (.request r) reply.request.input ++
      reply.hints.zipIdx.flatMap (fun (bytes,h) => byteQueries (.returned r h) bytes)) HookReply.payloadCost each
  simp only [byteQueries] at total
  omega

private theorem count_list_le (buffers : List Bytes) : buffers.length ≤ (buffers.map bytePayloadCost).sum := by
  induction buffers with
  | nil => simp
  | cons b bs ih => simp only [List.length_cons, List.map_cons, List.sum_cons, bytePayloadCost]; omega

private theorem count_hooks_le (replies : List HookReply) : replies.length ≤ (replies.map HookReply.payloadCost).sum := by
  induction replies with
  | nil => simp
  | cons r rs ih => simp only [List.length_cons, List.map_cons, List.sum_cons, HookReply.payloadCost, bytePayloadCost]; omega

private theorem sane_bytes {s : WriteStreams} {key : StreamKey} {bytes : Bytes} (read : key.contents s = some bytes)
    (reply : key.coordinates.2.1 < 2^48) (hint : key.coordinates.2.2 < 2^48) (size : bytes.length < 2^48)
    {q : Query} (member : q ∈ byteQueries key bytes) : ∃ v, q.lookup s = some v ∧ q.Fits v := by
  simp only [byteQueries, List.mem_cons, List.mem_map, List.mem_range] at member
  rcases member with rfl | ⟨i, bound, rfl⟩
  · exact ⟨bytes.length, by simp [Query.lookup, read], reply, hint, by change 0 < 2^48; decide, size⟩
  · exact ⟨bytes[i].toNat, by simp [Query.lookup, read, List.getElem?_eq_getElem bound], reply, hint,
      bound.trans size, bytes[i].isLt.trans (by decide)⟩

/-- The endpoint byte measure rules out all missing lookups and every coordinate/metadata wrap. -/
theorem inventoryOK_of_cost (s : WriteStreams) (bytes : streamCost s < 2^48) : inventoryOK s = true := by
  refine (inventoryOK_iff _).mpr ⟨(count_queries s).trans_lt bytes, ?_⟩
  intro q member
  simp only [queries, List.mem_append] at member
  unfold streamCost at bytes
  rcases member with ((out | err) | pub) | hooks
  · exact sane_bytes (key := .stdout) rfl (by decide) (by decide) (by omega) out
  · exact sane_bytes (key := .stderr) rfl (by decide) (by decide) (by omega) err
  · exact sane_bytes (key := .publicOutput) rfl (by decide) (by decide) (by omega) pub
  · obtain ⟨⟨reply, r⟩, atReply, inside⟩ := List.mem_flatMap.mp hooks
    have selected : s.hooks[r]? = some reply := List.mk_mem_zipIdx_iff_getElem?.mp atReply
    have rBound : r < 2^48 := by have := (List.getElem?_eq_some_iff.mp selected).1; have := count_hooks_le s.hooks; omega
    have cost := List.le_sum_of_mem (List.mem_map_of_mem (f := HookReply.payloadCost) (List.mem_of_getElem? selected))
    simp only [HookReply.payloadCost, bytePayloadCost, hintPayloadCost] at cost
    have hints := count_list_le reply.hints
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with ((rfl | rfl) | req) | returned
    · exact ⟨reply.request.descriptor.toNat, by simp [Query.lookup, selected], rBound, by change 0 < 2^48; decide, by change 0 < 2^48; decide, reply.request.descriptor.isLt.trans (by decide)⟩
    · exact ⟨reply.hints.length, by simp [Query.lookup, selected], rBound, by change 0 < 2^48; decide, by change 0 < 2^48; decide, by omega⟩
    · exact sane_bytes (key := .request r) (by simp [StreamKey.contents, selected]) rBound (by change 0 < 2^48; decide) (by omega) req
    · obtain ⟨⟨buf, h⟩, atHint, entries⟩ := List.mem_flatMap.mp returned
      have hint : reply.hints[h]? = some buf := List.mk_mem_zipIdx_iff_getElem?.mp atHint
      have hintCost := List.le_sum_of_mem (List.mem_map_of_mem (f := bytePayloadCost) (List.mem_of_getElem? hint))
      change 8 + buf.length ≤ (reply.hints.map bytePayloadCost).sum at hintCost
      exact sane_bytes (key := .returned r h) (by simp [StreamKey.contents, selected, hint]) rBound
        (by change h < 2^48; have := (List.getElem?_eq_some_iff.mp hint).1; omega) (by change buf.length < 2^48; omega) entries

private theorem take_cost (n : Nat) (rs : List HookReply) : ((rs.take n).map HookReply.payloadCost).sum ≤ (rs.map HookReply.payloadCost).sum := by
  have all := congrArg (fun l : List HookReply => (l.map HookReply.payloadCost).sum) (List.take_append_drop n rs)
  simp only [List.map_append, List.sum_append] at all
  omega

theorem streamCost_endpoints (source target : HostState) :
    streamCost (.fromEndpoints source target) ≤ source.payloadCost + target.payloadCost := by
  have used := take_cost (source.replies.length - target.replies.length) source.replies
  simp only [streamCost, WriteStreams.fromEndpoints, List.length_drop, HostState.payloadCost, bytePayloadCost]
  omega

/-- Native semantic resource ceilings imply representability for every fixed endpoint position.
The resulting table height also fits the backend's u64 index. -/
theorem admissible_inventoryOK {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    inventoryOK (.fromEndpoints source.host target.host) = true := by
  have low := run.2.2.2.1 .boundaryBytes
  have high := run.2.2.2.2.1 .boundaryBytes
  change source.realize.boundaryPayload ≤ SP1Prime - 1 at low
  change target.realize.boundaryPayload ≤ SP1Prime - 1 at high
  simp only [ExecutionState.boundaryPayload] at low high
  have a : source.realize.host = source.host := rfl
  have b : target.realize.host = target.host := rfl
  rw [a] at low
  rw [b] at high
  apply inventoryOK_of_cost
  have cost := streamCost_endpoints source.host target.host
  have field : SP1Prime < 2^31 := by decide
  omega

end SP1Clean.WriteEffects
