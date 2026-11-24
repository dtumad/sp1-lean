import SP1Clean.Export.WriteAllocationOrder

/-! # Contiguous fresh identities in the single physical queue history

Batch order is transported along the actual global queue permutation. HINT_READ and
HINT_LEN preserve the permanent frontier; every allocated node advances it by exactly one.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation HostHintQueue
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private def pointer (row : Step F) : Nat := Address.toNat row.node.node.pointer

private theorem batch_frontier {batch : List (Step F)} {a b : Cursor F}
    (walk : Walk.IsWalk (fun r : Step F => (r.before,r.after)) a b batch) (valid : ∀ r ∈ batch, r.Valid) :
    batch.map pointer = List.range' (Address.toNat a.state.allocated + 1) batch.length ∧
      Address.toNat b.state.allocated = Address.toNat a.state.allocated + batch.length := by
  induction batch generalizing a with
  | nil =>
    change a = b at walk
    simp [walk]
  | cons r rs ih =>
    obtain ⟨h,w⟩ := walk
    change r.before = a at h
    subst a
    obtain ⟨order,final⟩ := ih w (fun x mem => valid x (List.mem_cons_of_mem r mem))
    have step : pointer r = Address.toNat r.before.state.allocated + 1 := (valid r List.mem_cons_self).2.1.2.2.2.2.2
    change rs.map pointer = List.range' (pointer r + 1) rs.length at order
    change Address.toNat b.state.allocated = pointer r + rs.length at final
    simp only [List.length_cons,List.map_cons,List.range'_succ,order,step]
    exact ⟨trivial,by omega⟩

private def Follows (op : QueueOperation) (batch : List (Step F)) : Prop :=
  batch.map pointer = List.range' (Address.toNat (queueEdge op).1.allocated + 1) batch.length ∧
  Address.toNat (queueEdge op).2.allocated = Address.toNat (queueEdge op).1.allocated + batch.length

private theorem flatten_frontier {ops : List QueueOperation} {batches : List (List (Step F))}
    (follows : List.Forall₂ Follows ops batches) {a b : State F} (walk : Walk.IsWalk queueEdge a b ops) :
    batches.flatten.map pointer = List.range' (Address.toNat a.allocated + 1) batches.flatten.length ∧
    Address.toNat b.allocated = Address.toNat a.allocated + batches.flatten.length := by
  induction follows generalizing a with
  | nil =>
    change a = b at walk
    simp [walk]
  | @cons op batch rest tail paired _ ih =>
    obtain ⟨fromEq,step⟩ := walk
    subst a
    obtain ⟨first,next⟩ := paired
    obtain ⟨more,last⟩ := ih step
    simp only [List.flatten_cons,List.length_append,List.map_append,first,more,next] at last ⊢
    refine ⟨?_,by omega⟩
    rw [show Address.toNat (queueEdge op).1.allocated + batch.length + 1 =
      Address.toNat (queueEdge op).1.allocated + 1 + batch.length by omega,List.range'_append_1]

private theorem no_nodes (a b : ℕ) (same : b = a) :
    ([] : List (Step F)).map pointer = List.range' (a + 1) 0 ∧ b = a + 0 := by simp [same]

private theorem empty_handler (r : HostQueueOrder.Row (p := SP1Prime))
    (frontier : (HostQueueOrder.edge r).2.allocated = (HostQueueOrder.edge r).1.allocated) :
    Follows (.inl r) [] :=
  no_nodes _ _ (congrArg Address.toNat frontier)

private theorem handler_ranges (hs : List (HostQueueOrder.Row (p := SP1Prime)))
    (oldFrontiers : ∀ r ∈ hs, (HostQueueOrder.edge r).2.allocated = (HostQueueOrder.edge r).1.allocated) :
    List.Forall₂ Follows (hs.map Sum.inl) (hs.map (fun _ => [])) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r mem
    exact empty_handler r (oldFrontiers r mem)

private theorem node_ranges (calls : List (Open F)) (nodes : List (Step F)) (batches : List (List (Step F)))
    (paired : List.Forall₂ (fun (call : Open F) batch =>
      Walk.IsWalk (fun r : Step F => (r.before,r.after)) call.first call.last batch ∧
      batch.length = Address.toNat call.count) calls batches)
    (used : batches.flatten.Perm nodes) (valid : ∀ r ∈ nodes, r.Valid) :
    List.Forall₂ Follows (calls.map Sum.inr) batches := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_iff_zip.mpr
    refine ⟨paired.length_eq,?_⟩
    intro r batch m
    apply batch_frontier ((List.forall₂_iff_zip.mp paired).2 m).1
    intro x live
    exact valid x (used.mem_iff.mp
      (List.mem_flatten.mpr ⟨batch,(List.of_mem_zip m).2,live⟩))

private theorem chronological_frontier (hs : List (HostQueueOrder.Row (p := SP1Prime)))
    (calls : List (Open F)) (nodes : List (Step F)) (batches : List (List (Step F)))
    (path : List QueueOperation) (start finish : State F)
    (allOps : path.Perm (hs.map Sum.inl ++ calls.map Sum.inr))
    (walk : Walk.IsWalk queueEdge start finish path)
    (paired : List.Forall₂ (fun (call : Open F) batch =>
      Walk.IsWalk (fun r : Step F => (r.before,r.after)) call.first call.last batch ∧
      batch.length = Address.toNat call.count) calls batches)
    (used : batches.flatten.Perm nodes) (valid : ∀ r ∈ nodes, r.Valid)
    (oldFrontiers : ∀ r ∈ hs, (HostQueueOrder.edge r).2.allocated = (HostQueueOrder.edge r).1.allocated) :
    ∃ rows : List (Step F), rows.Perm nodes ∧
      rows.map (fun r => Address.toNat r.node.node.pointer) = List.range' (Address.toNat start.allocated + 1) rows.length ∧
      Address.toNat finish.allocated = Address.toNat start.allocated + rows.length := by
  have old := handler_ranges hs oldFrontiers
  have fresh := node_ranges calls nodes batches paired used valid
  obtain ⟨chronological,ordered,allBatches⟩ := List.perm_comp_forall₂ allOps (List.rel_append old fresh)
  have nodes := allBatches.flatten
  have empty : (hs.map (fun _ => ([] : List (Step F)))).flatten = [] := by simp
  rw [List.flatten_append,empty,List.nil_append] at nodes
  exact ⟨chronological.flatten,nodes.trans used,flatten_frontier ordered walk⟩

/-- The physical persistent node pointers are precisely one contiguous range after the
incoming frontier, in global queue order. Its length fixes the terminal seal frontier. -/
theorem native_allocation_frontier (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    let start := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) source.host.io.hints
    ∃ rows : List (Step F), rows.Perm (allocationInputs seen).2 ∧
      rows.map (fun r => Address.toNat r.node.node.pointer) = List.range' (Address.toNat start.allocated + 1) rows.length ∧
      Address.toNat (finalQueue seen).allocated = Address.toNat start.allocated + rows.length := by
  let seen := observed w
  let hs := hintHandlerRows seen
  let ins := allocationInputs seen
  obtain ⟨path,allOps,walk,_⟩ := native_ordered_queue w checked fit raw
  obtain ⟨batches,paired,used⟩ := native_matched_allocations w checked fit raw
  exact chronological_frontier hs ins.1 ins.2 batches path _ _ allOps walk paired used
    (allocation_endpoints w checked fit raw).2 (fun r m => (handler_facts seen ((observed_constraints w).mp checked) r m).2)

end SP1Clean.Export.WriteObservationAssembly
