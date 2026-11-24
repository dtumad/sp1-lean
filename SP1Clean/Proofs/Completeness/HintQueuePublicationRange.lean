import SP1Clean.Proofs.Completeness.WriteWitnessPosition
import SP1Clean.Proofs.Completeness.WriteWitnessInputs
import SP1Clean.Proofs.Completeness.HintQueueFixedReaders

/-! # Exact immutable publication range for a fresh WRITE allocation

At every physical row, the emitted metadata, padded word, and independent queue reader counts are those of the
one genuine pointer and byte buffer. Hook returns allocate pointers in reverse buffer order; both directions of
the pointer lookup therefore agree with the same final persistent store.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

/-- The two immutable queue sites and the actual reader count carried by each site. -/
structure Publication where
  /-- Counted node metadata. -/
  node : F × NodeRecord F
  /-- Counted words in zero-based padded position order. -/
  words : List (F × WordRecord F)

/-- Project the actual emitted payloads of an allocated node and its words. -/
def publication (rows : NodeRows) : Publication :=
  ⟨(rows.step.readers,rows.step.node.node),rows.words.map (fun w => (w.wordReads,w.word))⟩

/-- The expected immutable publisher at a single pointer in a persistent store. -/
def storedPublication (readers : Readers) (store : Store) (index : Nat) : Publication :=
  let node := (node? store (index+1)).getD default
  let nr := NodeRecord.encode (p := SP1Prime) (index+1) node
  let wr := fun i => WordRecord.encode (p := SP1Prime) (index+1) node.bytes i
  ⟨(readers.nodes nr,nr), List.ofFn (fun i : Fin (wordCount node.bytes) => (readers.words (wr i.val),wr i.val))⟩

/-- Every index of this physical batch is the corresponding permanent post-call allocation;
later queue mutations preserve the exact metadata, padded word data and assigned reader counts. -/
theorem batch_publications (batch : Batch) (previous clk : Nat) (store : Store) (head : Nat) (hints : List Bytes)
    (rep : Represents store head hints) (space : store.size + batch.buffers.length < 2^48)
    (sizes : ∀ b ∈ batch.buffers, b.length < 2^48) (readers : Readers) (last : Store)
    (extendsAfter : Extends (prepend store head batch.buffers).1 last) :
    ((batch.rows previous clk (store,head) readers).nodes.map publication) =
      (List.range' store.size batch.buffers.length).map (storedPublication readers last) := by
  apply List.ext_getElem
  · simp [Batch.rows_length]
  intro i left right
  have inside : i < batch.buffers.length := by simpa only [List.length_map,List.length_range'] using right
  let b := batch.buffers.reverse[i]'(by simp [inside])
  let ptr := store.size + i + 1
  let node : Node := ⟨b,if i=0 then head else store.size + i⟩
  have addr : ptr < 2^48 := by dsimp [ptr]; omega
  have source : batch.buffers.reverse[i]? = some b := List.getElem?_eq_getElem (by simp [inside])
  have found : node? last ptr = some node := extendsAfter _ _ (node?_prepend_at store head batch.buffers source)
  obtain ⟨step,atStep,_,_,_,pointer,_,_,count,record⟩ := batch.steps_at clk store head hints rep space sizes readers.nodes ⟨i,inside⟩
  have atRows : (batch.rows previous clk (store,head) readers).nodes[i]? = some (nodeRows readers step b) := by
    simp only [Batch.rows,List.getElem?_zipWith,atStep,source]
  obtain ⟨_,atRow⟩ := List.getElem_of_getElem? atRows
  simp only [List.getElem_map,List.getElem_range',Nat.one_mul,atRow]
  change (nodeRows readers step b |> publication) = storedPublication readers last (store.size + i)
  simp only [storedPublication,show store.size + i + 1 = ptr from rfl, found,Option.getD_some]
  change step.node.node = NodeRecord.encode ptr node at record
  have arr : Address.Bounded step.contents.pointer := pointer ▸ Address.bounded_ofNat _
  have key : Address.toNat step.contents.pointer = ptr := pointer ▸ Address.toNat_ofNat _ addr
  have words (j : Fin (wordCount b)) (br wr : F) :
      (Words.populate step.contents b j.val br wr).word = WordRecord.encode ptr b j.val := by
    rw [Words.populate_word _ _ _ br wr arr j.isLt,key]
  unfold publication nodeRows Words.walk
  simp only [count,record,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change (readers.words (Words.populate step.contents b i.val 0 0).word,
    (Words.populate step.contents b i.val _ _).word) = _
  simp only [words]
  rfl

end SP1Clean.WriteEffects.Witness
