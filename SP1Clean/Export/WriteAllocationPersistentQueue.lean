import SP1Clean.Export.WriteAllocationPhysicalWords
import SP1Clean.Soundness.AllocationWordPartition

/-! # The persistent hint store recovered from arbitrary accepted native rows -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Every actual freshly allocated node owns a complete word walk. The partition retains
all active rows, including zero-reader nodes and the empty last word of aligned buffers. -/
theorem native_allocation_word_walks (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃ paths : List (List (Words.Row F)),
      List.Forall₂ (fun r rs => Walk.IsWalk Words.wordEdge (some (Words.start r.contents)) none rs)
        (allocationInputs (observed w)).2 paths ∧ paths.flatten.Perm (allocationWords (observed w)) := by
  obtain ⟨ends,valid⟩ := native_word_endpoints w checked fit raw
  obtain ⟨paths,walking,used⟩ := Words.partition _ _ ends valid
  obtain ⟨ordered,correct,reordered⟩ := List.perm_comp_forall₂ (native_word_seeds w checked fit raw) walking
  exact ⟨ordered,List.forall₂_map_left_iff.mp correct,reordered.flatten.trans used⟩

private theorem attach_bytes {nodes : List (Step F)} {paths : List (List (Words.Row F))}
    (walks : List.Forall₂ (fun r rs => Walk.IsWalk Words.wordEdge (some (Words.start r.contents)) none rs) nodes paths)
    (unique : nodes.Nodup) (valid : ∀ r ∈ paths.flatten, r.Valid) :
    ∃ bytes : Step F → Bytes, (∀ r ∈ nodes, (bytes r).length = Address.toNat r.length) ∧
      ∀ word ∈ paths.flatten, ∃ r ∈ nodes,
        word.word ∈ nodeWordRows (p := SP1Prime) (Address.toNat r.node.node.pointer) (bytes r) := by
  classical
  induction walks with
  | nil => exact ⟨fun _ => [],by simp,by simp⟩
  | @cons n path ns rest first _ ih =>
    obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp unique
    obtain ⟨bytes,lengths,records⟩ := ih distinct (fun r mem => valid _ (List.mem_append_right path mem))
    obtain ⟨size,values⟩ := Words.decode_walk n.contents path first (fun r mem => valid _ (List.mem_append_left _ mem))
    let attach := fun r => if r = n then Words.decodedBytes n.contents path else bytes r
    refine ⟨attach,?_,?_⟩
    · intro r present
      rcases List.mem_cons.mp present with same | old
      · subst r; simpa only [attach,ite_eq_left rfl,Step.contents] using size
      · have other : r ≠ n := fun eq => fresh (eq ▸ old)
        simpa only [attach,ite_eq_right other] using lengths r old
    · intro r present
      rcases List.mem_append.mp present with newWord | oldWord
      · exact ⟨n,List.mem_cons_self,by simpa only [attach,ite_eq_left rfl,Step.contents] using values r newWord⟩
      · obtain ⟨owner,mem,word⟩ := records _ oldWord
        have other : owner ≠ n := fun eq => fresh (eq ▸ mem)
        exact ⟨owner,List.mem_cons_of_mem _ mem,by simpa only [attach,ite_eq_right other] using word⟩

/-- Every accepted native segment determines an immutable store extending the incoming
snapshot. All its active node and word publications name this same store, and walking the
physical final head recovers the entire public outgoing hint queue. -/
theorem native_persistent_queue (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) : ∃ store, PersistentQueue w store := by
  obtain ⟨paths,walks,used⟩ := native_allocation_word_walks w checked fit raw
  obtain ⟨bytes,lengths,funded⟩ := attach_bytes walks
    (List.Nodup.of_map _ (native_node_pointers_unique w checked fit raw))
    (fun r mem => (native_word_endpoints w checked fit raw).2 r (used.mem_iff.mp mem))
  exact persistent_queue_of_decoded_words w checked fit raw bytes lengths
    (fun r mem => funded r (used.mem_iff.mpr mem))

end SP1Clean.Export.WriteObservationAssembly
