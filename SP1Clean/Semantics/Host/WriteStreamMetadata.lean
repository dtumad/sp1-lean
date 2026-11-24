module

public import SP1Clean.Semantics.Host.WriteStreamBlocks

/-! # Compact metadata accompanying word-sized WRITE data

Lengths, hook descriptors and return counts are represented once. No per-byte metadata row is
materialized. The actual output and returned bytes live in the separate aligned block inventory.
-/

@[expose] public section

namespace SP1Clean.WriteEffects
open Semantics

def Query.IsMetadata : Query → Prop
  | .byte .. => False
  | _ => True

def metadataRows {p : Nat} (s : WriteStreams) : List (Record (ZMod p)) :=
  [(Query.length .stdout).encode s.stdout.length, (Query.length .stderr).encode s.stderr.length,
   (Query.length .publicOutput).encode s.publicOutput.length] ++
    s.hooks.zipIdx.flatMap fun (reply,r) =>
      [(Query.descriptor r).encode reply.request.descriptor.toNat, (Query.returnCount r).encode reply.hints.length,
       (Query.length (.request r)).encode reply.request.input.length] ++
      reply.hints.zipIdx.map (fun (b,h) => (Query.length (.returned r h)).encode b.length)

/-- The compact inventory includes all metadata, including lengths of empty returned hints. -/
theorem metadataRows_iff {p : Nat} (s : WriteStreams) (row : Record (ZMod p)) :
    row ∈ metadataRows s ↔ ∃ (q : Query) (v : Nat), q.IsMetadata ∧ q.lookup s = some v ∧ row = q.encode v := by
  constructor
  · intro mem
    simp only [metadataRows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with (rfl | rfl | rfl) | hook
    · exact ⟨.length .stdout,_,trivial,rfl,rfl⟩
    · exact ⟨.length .stderr,_,trivial,rfl,rfl⟩
    · exact ⟨.length .publicOutput,_,trivial,rfl,rfl⟩
    obtain ⟨⟨reply,r⟩,atReply,placed⟩ := List.mem_flatMap.mp hook
    have found := List.mk_mem_zipIdx_iff_getElem?.mp atReply
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at placed
    rcases placed with (rfl | rfl | rfl) | hint
    · exact ⟨.descriptor r,_,trivial,by simp [Query.lookup,found],rfl⟩
    · exact ⟨.returnCount r,_,trivial,by simp [Query.lookup,found],rfl⟩
    · exact ⟨.length (.request r),_,trivial,by simp [Query.lookup,StreamKey.contents,found],rfl⟩
    · obtain ⟨⟨bytes,h⟩,atHint,rfl⟩ := List.mem_map.mp hint
      exact ⟨.length (.returned r h),_,trivial,
        by simp [Query.lookup,StreamKey.contents,found,List.mk_mem_zipIdx_iff_getElem?.mp atHint],rfl⟩
  · rintro ⟨q,v,isMeta,found,rfl⟩
    cases q with
    | byte => exact isMeta.elim
    | descriptor r =>
      obtain ⟨reply,ok,rfl⟩ := Option.map_eq_some_iff.mp found
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r),List.mk_mem_zipIdx_iff_getElem?.mpr ok,List.mem_append_left _ List.mem_cons_self⟩)
    | returnCount r =>
      obtain ⟨reply,ok,rfl⟩ := Option.map_eq_some_iff.mp found
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r),List.mk_mem_zipIdx_iff_getElem?.mpr ok,List.mem_append_left _ (by simp)⟩)
    | length key =>
      obtain ⟨bytes,read,rfl⟩ := Option.map_eq_some_iff.mp found
      cases key with
      | stdout => cases read; simp [metadataRows]
      | stderr => cases read; simp [metadataRows]
      | publicOutput => cases read; simp [metadataRows]
      | request r =>
        obtain ⟨reply,ok,rfl⟩ := Option.map_eq_some_iff.mp read
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r),List.mk_mem_zipIdx_iff_getElem?.mpr ok,List.mem_append_left _ (by simp)⟩)
      | returned r h =>
        obtain ⟨reply,ok,hint⟩ := Option.bind_eq_some_iff.mp read
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r),List.mk_mem_zipIdx_iff_getElem?.mpr ok,List.mem_append_right _
          (List.mem_map.mpr ⟨(bytes,h),List.mk_mem_zipIdx_iff_getElem?.mpr hint,rfl⟩)⟩)

private theorem le_flatMap {α β : Type} (xs : List α) (rows : α → List β) (positive : ∀ x, 1 ≤ (rows x).length) :
    xs.length ≤ (xs.flatMap rows).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.length_cons,List.flatMap_cons,List.length_append]; have := positive x; omega

/-- Exact physical record count, independent of the number of payload bytes. -/
theorem metadataRows_length {p : Nat} (s : WriteStreams) :
    (metadataRows (p := p) s).length = 3 + (s.hooks.map fun r => 3 + r.hints.length).sum := by
  simp only [metadataRows,List.length_append,List.length_cons,List.length_nil,List.length_flatMap,List.length_map,List.length_zipIdx]
  congr 1
  change (s.hooks.zipIdx.map ((fun (r : HookReply) => 3 + r.hints.length) ∘ Prod.fst)).sum = _
  rw [← List.map_map,List.zipIdx_map_fst]

theorem metadataRows_le_queries {p : Nat} (s : WriteStreams) :
    (metadataRows (p := p) s).length ≤ (queries s).length := by
  unfold metadataRows queries
  simp only [List.length_append,List.length_cons,List.length_nil]
  have hook (r : Nat) (reply : HookReply) :
      3 + reply.hints.length ≤ ([Query.descriptor r,.returnCount r] ++ byteQueries (.request r) reply.request.input ++
        reply.hints.zipIdx.flatMap (fun y => byteQueries (.returned r y.2) y.1)).length := by
    have hints := le_flatMap reply.hints.zipIdx (fun y => byteQueries (.returned r y.2) y.1) (by intros; simp [byteQueries])
    simp only [List.length_zipIdx] at hints
    simp only [List.length_append,List.length_cons,List.length_nil]
    have positive : 1 ≤ (byteQueries (.request r) reply.request.input).length := by simp [byteQueries]
    omega
  have total (xs : List (HookReply × Nat)) :
      (xs.flatMap fun y => [(Query.descriptor y.2).encode (p := p) y.1.request.descriptor.toNat,
        (Query.returnCount y.2).encode y.1.hints.length,(Query.length (.request y.2)).encode y.1.request.input.length] ++
        y.1.hints.zipIdx.map fun z => (Query.length (.returned y.2 z.2)).encode z.1.length).length ≤
      (xs.flatMap fun y => [Query.descriptor y.2,.returnCount y.2] ++ byteQueries (.request y.2) y.1.request.input ++
        y.1.hints.zipIdx.flatMap fun z => byteQueries (.returned y.2 z.2) z.1).length := by
    induction xs with
    | nil => simp
    | cons y ys ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_zipIdx] at *
      have bound := hook y.2 y.1
      omega
  have bound := total s.hooks.zipIdx
  have pos (k : StreamKey) (b : Bytes) : 1 ≤ (byteQueries k b).length := by simp [byteQueries]
  have := pos .stdout s.stdout
  have := pos .stderr s.stderr
  have := pos .publicOutput s.publicOutput
  omega

end SP1Clean.WriteEffects
