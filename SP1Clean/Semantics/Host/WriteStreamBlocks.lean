module

public import SP1Clean.Semantics.Host.WriteStreamRecords
public import SP1Clean.Semantics.Host.HintQueueWords

/-! # Word-sized fixed WRITE stream inventory

Each nonempty stream contributes one record per group of up to eight consecutive bytes.
The final block carries its actual extent and fills the remaining lanes with zero. Empty
streams keep their length metadata and generate no data blocks.
-/

@[expose] public section

namespace SP1Clean.WriteEffects
open Semantics

/-- Enumerate each actual byte string once, including empty requests and empty returned hints. -/
def buffers (s : WriteStreams) : List (StreamKey × Bytes) :=
  [(.stdout, s.stdout), (.stderr, s.stderr), (.publicOutput, s.publicOutput)] ++
    s.hooks.zipIdx.flatMap fun (reply,r) => (.request r, reply.request.input) ::
      reply.hints.zipIdx.map (fun (bytes,h) => (.returned r h, bytes))

theorem buffers_iff (s : WriteStreams) (key : StreamKey) (bytes : Bytes) :
    (key,bytes) ∈ buffers s ↔ key.contents s = some bytes := by
  constructor
  · intro mem
    simp only [buffers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with (h | h | h) | hooks
    all_goals try cases h; rfl
    obtain ⟨⟨reply,r⟩, atReply, placed⟩ := List.mem_flatMap.mp hooks
    have found := List.mk_mem_zipIdx_iff_getElem?.mp atReply
    rcases List.mem_cons.mp placed with h | others
    · cases h
      simp [StreamKey.contents, found]
    · obtain ⟨⟨buf,h⟩, atHint, eq⟩ := List.mem_map.mp others
      cases eq
      simp [StreamKey.contents, found, List.mk_mem_zipIdx_iff_getElem?.mp atHint]
  · intro found
    cases key with
    | stdout => cases found; simp [buffers]
    | stderr => cases found; simp [buffers]
    | publicOutput => cases found; simp [buffers]
    | request r =>
      obtain ⟨reply, ok, rfl⟩ := Option.map_eq_some_iff.mp found
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r), List.mk_mem_zipIdx_iff_getElem?.mpr ok, List.mem_cons_self⟩)
    | returned r h =>
      obtain ⟨reply, ok, atHint⟩ := Option.bind_eq_some_iff.mp found
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(reply,r), List.mk_mem_zipIdx_iff_getElem?.mpr ok,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(bytes,h), List.mk_mem_zipIdx_iff_getElem?.mpr atHint, rfl⟩)⟩)

/-- Positional fixed payload, shared by outputs, hook requests and returned hints. -/
structure StreamBlock (F : Type) where
  /-- Tag identifying the output stream, hook request or returned hints. -/
  stream : F
  /-- Hook reply ordinal, or zero for an ordinary output. -/
  reply : fields 3 F
  /-- Returned-hint ordinal within a reply, or zero for the other streams. -/
  hint : fields 3 F
  /-- Zero-based block index within the identified byte string. -/
  index : fields 3 F
  /-- Number of occupied lanes, including a partial last block. -/
  used : F
  /-- Eight consecutive bytes with zero padding beyond the occupied lanes. -/
  bytes : fields 8 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas StreamBlock

/-- Number of eight-byte blocks needed to hold the actual bytes. -/
def blockCount (bytes : Bytes) : Nat := (bytes.length + 7) / 8

/-- Encode one block with its owner, index, occupied length and padded byte lanes. -/
def encodeBlock {p : Nat} (key : StreamKey) (bytes : Bytes) (index : Nat) : StreamBlock (ZMod p) :=
  let (tag,r,h) := key.coordinates
  ⟨tag, Address.ofNat r, Address.ofNat h, Address.ofNat index, (min 8 (bytes.length - 8 * index) : Nat),
    (HintQueue.wordBytes bytes index).map (fun b => (b.toNat : ZMod p))⟩

/-- All aligned blocks of the endpoint outputs, hook inputs and returned buffers. -/
def dataBlocks {p : Nat} (s : WriteStreams) : List (StreamBlock (ZMod p)) :=
  (buffers s).flatMap fun (key,bytes) => (List.range (blockCount bytes)).map (encodeBlock key bytes)

/-- Raw table entries are precisely the blocks of actual strings at actual aligned positions. -/
theorem dataBlocks_iff {p : Nat} (s : WriteStreams) (block : StreamBlock (ZMod p)) :
    block ∈ dataBlocks s ↔ ∃ key bytes index, key.contents s = some bytes ∧ 8 * index < bytes.length ∧ block = encodeBlock key bytes index := by
  constructor
  · intro mem
    obtain ⟨⟨key,bytes⟩, owner, present⟩ := List.mem_flatMap.mp mem
    obtain ⟨index, bound, rfl⟩ := List.mem_map.mp present
    have lt := List.mem_range.mp bound
    change index < (bytes.length + 7)/8 at lt
    exact ⟨key,bytes,index,(buffers_iff ..).mp owner,by omega,rfl⟩
  · rintro ⟨key,bytes,index,owner,bound,rfl⟩
    exact List.mem_flatMap.mpr ⟨(key,bytes),(buffers_iff ..).mpr owner,List.mem_map.mpr
      ⟨index,List.mem_range.mpr (by change index < (bytes.length + 7)/8; omega), rfl⟩⟩

theorem encodeBlock_fields {p : Nat} [Fact p.Prime] [Fact (2^17 < p)] (s : WriteStreams)
    (checked : inventoryOK s = true) {key : StreamKey} {bytes : Bytes} {index : Nat}
    (owner : key.contents s = some bytes) (active : 8 * index < bytes.length) :
    let block := encodeBlock (p := p) key bytes index
    block.stream.val = key.coordinates.1 ∧ Address.toNat block.reply = key.coordinates.2.1 ∧
    Address.toNat block.hint = key.coordinates.2.2 ∧ Address.toNat block.index = index ∧
    block.used.val = min 8 (bytes.length-8 * index) ∧
    ∀ i : Fin 8, block.bytes[i].val = (bytes[index * 8 + i.val]?.getD 0).toNat := by
  have read : (Query.length key).lookup s = some bytes.length := by simp [Query.lookup, owner]
  obtain ⟨v,found,coords⟩ := ((inventoryOK_iff _).mp checked).2 _ (Query.enumerated read)
  obtain rfl := Option.some.inj (found.symm.trans read)
  obtain ⟨rb,hb,_,size⟩ := coords
  have hp : 2^17 < p := Fact.out
  have tag : key.coordinates.1 < p := by cases key <;> simp only [StreamKey.coordinates] <;> omega
  refine ⟨ZMod.val_natCast_of_lt tag, Address.toNat_ofNat _ rb, Address.toNat_ofNat _ hb,
    Address.toNat_ofNat _ (by omega), ZMod.val_natCast_of_lt (by have := Nat.min_le_left 8 (bytes.length - 8 * index); omega), ?_⟩
  intro i
  simp only [encodeBlock, HintQueue.wordBytes, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
  apply ZMod.val_natCast_of_lt
  have := (bytes[index * 8 + i.val]?.getD 0).isLt
  omega

/-- The same byte is recovered from its canonical block, even at either end of a partial block. -/
theorem lookup_in_block {p : Nat} [Fact p.Prime] [Fact (2^17 < p)] {s : WriteStreams} (checked : inventoryOK s = true)
    {key : StreamKey} {bytes : Bytes} {pos : Nat} {byte : BitVec 8} (owner : key.contents s = some bytes)
    (found : bytes[pos]? = some byte) :
    ∃ block ∈ dataBlocks (p := p) s, block = encodeBlock key bytes (pos/8) ∧
      block.bytes[(⟨pos%8,Nat.mod_lt _ (by decide)⟩ : Fin 8)].val = byte.toNat ∧ pos%8 < block.used.val := by
  have lt := (List.getElem?_eq_some_iff.mp found).1
  have active : 8 * (pos / 8) < bytes.length := by omega
  let encoded := encodeBlock (p := p) key bytes (pos/8)
  obtain ⟨_,_,_,_,valid,lanes⟩ := encodeBlock_fields (p := p) s checked owner active
  let lane : Fin 8 := ⟨pos%8,Nat.mod_lt _ (by decide)⟩
  have location : pos / 8 * 8 + lane.val = pos := by dsimp [lane]; omega
  refine ⟨encoded,(dataBlocks_iff ..).mpr ⟨key,bytes,pos/8,owner,active,rfl⟩,rfl,?_,?_⟩
  · simpa only [location,found,Option.getD_some] using lanes lane
  · rw [valid]; omega

private theorem flat_lengths_mono {α β γ : Type} (xs : List α) (left : α → List β) (right : α → List γ)
    (le : ∀ x, (left x).length ≤ (right x).length) :
    (xs.flatMap left).length ≤ (xs.flatMap right).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append]
    exact Nat.add_le_add (le x) ih

private def blocksFor {p : Nat} (key : StreamKey) (bytes : Bytes) :=
  (List.range (blockCount bytes)).map (encodeBlock (p := p) key bytes)

private theorem blocksFor_length {p : Nat} (key : StreamKey) (bytes : Bytes) :
    (blocksFor (p := p) key bytes).length ≤ (byteQueries key bytes).length := by
  simp [blocksFor, byteQueries, blockCount]
  omega

theorem dataBlocks_length {p : Nat} (s : WriteStreams) :
    (dataBlocks (p := p) s).length ≤ (queries s).length := by
  change ((buffers s).flatMap (fun (key,b) => blocksFor (p := p) key b)).length ≤ _
  unfold buffers queries
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, List.flatMap_assoc]
  have hooks := flat_lengths_mono s.hooks.zipIdx
    (fun x => ((.request x.2,x.1.request.input) :: x.1.hints.zipIdx.map (fun y => (StreamKey.returned x.2 y.2,y.1))).flatMap
      (fun z => blocksFor (p := p) z.1 z.2))
    (fun x => [Query.descriptor x.2, .returnCount x.2] ++ byteQueries (.request x.2) x.1.request.input ++
      x.1.hints.zipIdx.flatMap (fun y => byteQueries (.returned x.2 y.2) y.1)) (by
      rintro ⟨reply,r⟩
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append, List.length_cons, List.length_nil ]
      have returned := flat_lengths_mono reply.hints.zipIdx (fun y => blocksFor (p := p) (.returned r y.2) y.1)
        (fun y => byteQueries (.returned r y.2) y.1) (fun _ => blocksFor_length ..)
      have request := blocksFor_length (p := p) (.request r) reply.request.input
      omega)
  simp only [List.flatMap_cons] at hooks
  have out := blocksFor_length (p := p) .stdout s.stdout
  have err := blocksFor_length (p := p) .stderr s.stderr
  have pub := blocksFor_length (p := p) .publicOutput s.publicOutput
  omega

end SP1Clean.WriteEffects
