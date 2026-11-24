import SP1Clean.Native.Operations.WriteSliceSource
import SP1Clean.Native.Operations.WriteBlockSource
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Completeness.WriteStreamCapacity

/-! # Paid table heights of fixed WRITE stream blocks and metadata

Each nonempty string rounds separately to groups of eight. The existing per-buffer length
charges cover all local partial blocks, including sequences of single-byte returned hints.
-/

namespace SP1Clean.WriteEffects
open Semantics Machine FormalModel.Shard

private theorem weighted_indexed {α β : Type} (weight : Nat) (xs : List α) (rows : α × Nat → List β)
    (cost : α → Nat) (paid : ∀ x i, weight * (rows (x,i)).length ≤ cost x) :
    weight * (xs.zipIdx.flatMap rows).length ≤ (xs.map cost).sum := by
  have same : (xs.zipIdx.map (fun x => cost x.1)).sum = (xs.map cost).sum := by
    change (xs.zipIdx.map (cost ∘ Prod.fst)).sum = _
    rw [← List.map_map,List.zipIdx_map_fst]
  rw [← same]
  induction xs.zipIdx with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (paid x.1 x.2) ih

private def blocksOf {p : Nat} (key : StreamKey) (bytes : Bytes) :=
  (List.range (blockCount bytes)).map (encodeBlock (p := p) key bytes)

private theorem blocksOf_paid {p : Nat} (key : StreamKey) (bytes : Bytes) :
    8 * (blocksOf (p := p) key bytes).length ≤ bytes.length + 7 := by
  simp only [blocksOf,List.length_map,List.length_range,blockCount]
  omega

/-- The three output strings can introduce at most 21 padding bytes; every individual
hook or returned hint pays for its own partially occupied last block. -/
theorem dataBlocks_paid {p : Nat} (s : WriteStreams) :
    8 * (dataBlocks (p := p) s).length ≤ streamCost s + 18 := by
  let render := fun (z : StreamKey × Bytes) => blocksOf (p := p) z.1 z.2
  let hook := fun (x : HookReply × Nat) =>
    ((StreamKey.request x.2,x.1.request.input) :: x.1.hints.zipIdx.map (fun y => (StreamKey.returned x.2 y.2,y.1))).flatMap render
  have hooks := weighted_indexed 8 s.hooks hook HookReply.payloadCost (by
    intro reply r
    have returned := weighted_indexed 8 reply.hints (fun x => blocksOf (p := p) (.returned r x.2) x.1) bytePayloadCost (by
      intro b h
      have bound := blocksOf_paid (p := p) (.returned r h) b
      change 8 * (blocksOf (p := p) (.returned r h) b).length ≤ 8 + b.length
      omega)
    have req := blocksOf_paid (p := p) (.request r) reply.request.input
    simp only [hook,render,List.flatMap_cons,List.flatMap_map,List.length_append,Nat.mul_add,
      HookReply.payloadCost,bytePayloadCost,hintPayloadCost]
    omega)
  change 8 * ((buffers s).flatMap render).length ≤ streamCost s + 18
  simp only [buffers,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.flatMap_assoc,List.length_append]
  change 8 * ((blocksOf (p := p) .stdout s.stdout).length +
    ((blocksOf (p := p) .stderr s.stderr).length + (blocksOf (p := p) .publicOutput s.publicOutput).length) +
    (s.hooks.zipIdx.flatMap hook).length) ≤ streamCost s + 18
  have out := blocksOf_paid (p := p) .stdout s.stdout
  have err := blocksOf_paid (p := p) .stderr s.stderr
  have pub := blocksOf_paid (p := p) .publicOutput s.publicOutput
  unfold streamCost
  omega

/-- Six bytes of representation budget pay for each actual metadata record, even when all
hook requests and returns are empty. The three fixed output lengths add a constant. -/
theorem metadataRows_paid {p : Nat} (s : WriteStreams) :
    6 * (metadataRows (p := p) s).length ≤ streamCost s + 15 := by
  have hints (l : List Bytes) : 8 * l.length ≤ (l.map bytePayloadCost).sum := by
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.length_cons,List.map_cons,List.sum_cons,bytePayloadCost]
      omega
  have charge (rs : List HookReply) :
      6 * (rs.map (fun r => 3 + r.hints.length)).sum ≤ (rs.map HookReply.payloadCost).sum := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.map_cons,List.sum_cons,HookReply.payloadCost,hintPayloadCost,bytePayloadCost]
      have paid := hints r.hints
      omega
  rw [metadataRows_length]
  unfold streamCost
  have all := charge s.hooks
  omega

/-- At the full semantic native boundary budgets, all preallocated heights fit without
restricting the admitted output bytes, request/reply count, or returned hint lengths. -/
theorem admissible_fixed_heights {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (blockTable (p := SP1Prime) (.fromEndpoints source.host target.host)).height ≤ 2^29 ∧
    (streamTable (p := SP1Prime) source.host target.host).height ≤ 2^30 ∧ (planTable (p := SP1Prime)).height = 512 := by
  let s := WriteStreams.fromEndpoints source.host target.host
  have shape := admissible_inventoryOK run
  have lo := run.2.2.2.1 .boundaryBytes
  have hi := run.2.2.2.2.1 .boundaryBytes
  change source.realize.boundaryPayload ≤ SP1Prime - 1 at lo
  change target.realize.boundaryPayload ≤ SP1Prime - 1 at hi
  simp only [ExecutionState.boundaryPayload] at lo hi
  have sl : source.realize.host = source.host := rfl
  have tl : target.realize.host = target.host := rfl
  rw [sl] at lo
  rw [tl] at hi
  have field : SP1Prime = 2130706433 := rfl
  have cost : streamCost s ≤ source.host.payloadCost + target.host.payloadCost := streamCost_endpoints ..
  have data := dataBlocks_paid (p := SP1Prime) s
  have metadataBound := metadataRows_paid (p := SP1Prime) s
  have blockRows : (blockTable (p := SP1Prime) s).length ≤ 2^29 := by
    change (if inventoryOK s then dataBlocks (p := SP1Prime) s else []).length ≤ _
    rw [ite_eq_left shape]
    omega
  have metaRows : (streamTable (p := SP1Prime) source.host target.host).length ≤ 2^30 := by
    change (if inventoryOK s then metadataRows (p := SP1Prime) s else []).length ≤ _
    rw [ite_eq_left shape]
    omega
  refine ⟨Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr blockRows),
    Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr metaRows),?_⟩
  have plan : (planTable (p := SP1Prime)).length = 352 := by
    change (slicePlans (p := SP1Prime)).length = _
    simp only [slicePlans,List.length_flatMap,List.length_map,List.length_range]
    decide
  rw [StaticTable.height,plan]
  decide

end SP1Clean.WriteEffects
