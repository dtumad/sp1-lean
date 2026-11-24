import SP1Clean.Proofs.Completeness.HintQueuePublishedHistory
import SP1Clean.Proofs.Completeness.HistoricalHintCapacity

/-! # Unique immutable providers for every fresh request

The post-source allocation interval contains exactly one node per permanent pointer and one padded word per
pointer and index. A typed read determines its canonical payload from the common final store even after a pop.
-/

namespace SP1Clean.TraceGen.HintQueueReaders
open Semantics HintQueue Machine FormalModel.Shard Soundness.Target
private abbrev F := ZMod SP1Prime

/-- Canonical node record at a zero-based permanent store index. -/
def nodeAt (store : Store) (i : Nat) : NodeRecord F :=
  NodeRecord.encode (i+1) ((node? store (i+1)).getD default)

/-- Canonical padded words at that same zero-based store index. -/
def wordsAt (store : Store) (i : Nat) : List (WordRecord F) :=
  let n := (node? store (i+1)).getD default
  List.ofFn (fun j : Fin (wordCount n.bytes) => WordRecord.encode (i+1) n.bytes j.val)

/-- Every physical publisher above the incoming frontier, including nodes that will have no consumers. -/
def fresh (store : Store) (initial : Nat) : Demand :=
  let indices := List.range' initial (store.size - initial)
  ⟨indices.map (nodeAt store),indices.flatMap (wordsAt store)⟩

/-- All typed requests above the incoming frontier have an actual node/word within the fresh published range. -/
theorem fresh_covered {store : Store} (initial : Nat) {d : Demand} (bound : d.Binds store) :
    let uses := d.select (fun ptr => initial < ptr)
    (∀ r ∈ uses.nodes, r ∈ (fresh store initial).nodes) ∧ (∀ r ∈ uses.words, r ∈ (fresh store initial).words) := by
  constructor
  · intro r use
    obtain ⟨member,above⟩ := List.mem_filter.mp use
    obtain ⟨valid,binding⟩ := bound.1 r member
    obtain ⟨n,found,same⟩ := node_canonical valid binding
    have within := (node?_bound found).2
    generalize ptr : Address.toNat r.pointer = k at above within found same
    cases k with
    | zero => contradiction
    | succ i =>
      have lo : initial < i+1 := of_decide_eq_true above
      apply List.mem_map.mpr
      exact ⟨i,List.mem_range'_1.mpr (by omega),by simpa [nodeAt,found] using same⟩
  · intro r use
    obtain ⟨member,above⟩ := List.mem_filter.mp use
    obtain ⟨valid,binding⟩ := bound.2 r member
    obtain ⟨n,found,j,same⟩ := word_canonical valid binding
    have within := (node?_bound found).2
    generalize ptr : Address.toNat r.pointer = k at above within found same
    cases k with
    | zero => contradiction
    | succ i =>
      have lo : initial < i+1 := of_decide_eq_true above
      apply List.mem_flatMap.mpr
      refine ⟨i,List.mem_range'_1.mpr (by omega),?_⟩
      simp only [wordsAt,found,Option.getD_some]
      exact List.mem_ofFn.mpr ⟨⟨_,j⟩,same⟩

/-- The native boundary's measured persistent inventory bounds all index and pointer encodings together. -/
theorem native_store_sizes {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {final : Store × Nat}
    (done : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final) :
    final.1.size < 2^48 ∧ ∀ i < final.1.size, wordCount (final.1[i]!).bytes ≤ 2^48 := by
  obtain ⟨_,_,_,_,endCursor,_,_,_,size,_⟩ := admissibleExecution_hintInventory run events.length
  rw [List.take_length] at endCursor
  cases Option.some.inj (done.symm.trans endCursor)
  obtain ⟨_,_,_,_,reached,_,_,_,_,_,_,_,_,paid,_⟩ := admissibleExecution_historicalHintCapacity run events.length
  rw [List.take_length] at reached
  cases Option.some.inj (done.symm.trans reached)
  refine ⟨size,?_⟩
  intro i used
  have inside : final.1[i] ∈ final.1.toList := Array.mem_toList_iff.mpr (Array.getElem_mem used)
  have wordLimit : wordCount final.1[i].bytes ≤ storedWordCount final.1 :=
    List.le_sum_of_mem (List.mem_map_of_mem (List.mem_map_of_mem (f := Node.bytes) inside))
  have width : SP1Prime < 2^31 := by decide
  rw [getElem!_pos final.1 i used]
  omega

/-- Distinct fresh physical positions have distinct full messages, even when bytes and tails repeat. -/
theorem fresh_unique (store : Store) (initial : Nat) (width : store.size < 2^48)
    (sizes : ∀ i < store.size, wordCount (store[i]!).bytes ≤ 2^48) :
    (fresh store initial).nodes.Nodup ∧ (fresh store initial).words.Nodup := by
  let indices := List.range' initial (store.size - initial)
  have within {x : Nat} (m : x ∈ indices) : x < store.size := by
    obtain ⟨_,hi⟩ := List.mem_range'_1.mp m
    by_cases order : initial ≤ store.size
    · omega
    · have lo := (List.mem_range'_1.mp m).1; omega
  have dec {i : Nat} (m : i ∈ indices) : Address.toNat (Address.ofNat (p := SP1Prime) (i+1)) = i+1 :=
    Address.toNat_ofNat _ (by have := within m; omega)
  have unique : indices.Nodup := List.nodup_range' _
  constructor
  · apply unique.map_on
    intro a ar b br eqn
    have same := congrArg (fun r : NodeRecord F => Address.toNat r.pointer) eqn
    change Address.toNat (Address.ofNat (a+1) : fields 3 F) = Address.toNat (Address.ofNat (b+1)) at same
    rw [dec ar,dec br] at same
    omega
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ar
    have inside := within ar
    have extent := sizes a inside
    have found : node? store (a+1) = some store[a] := Array.getElem?_eq_getElem inside
    rw [getElem!_pos store a inside] at extent
    simp only [wordsAt,found,Option.getD_some]
    apply List.nodup_ofFn.mpr
    intro x y eqn
    have same := congrArg (fun r : WordRecord F => Address.toNat r.index) eqn
    change Address.toNat (Address.ofNat x.val : fields 3 F) = Address.toNat (Address.ofNat y.val) at same
    rw [Address.toNat_ofNat _ (x.isLt.trans_le extent),Address.toNat_ofNat _ (y.isLt.trans_le extent)] at same
    exact Fin.ext same
  · apply unique.imp_of_mem
    intro a b ar br diff r left right
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp left
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp right
    have same := congrArg (fun r : WordRecord F => Address.toNat r.pointer) (hi.trans hj.symm)
    change Address.toNat (Address.ofNat (a+1) : fields 3 F) = Address.toNat (Address.ofNat (b+1)) at same
    rw [dec ar,dec br] at same
    exact diff (by omega)

end SP1Clean.TraceGen.HintQueueReaders
