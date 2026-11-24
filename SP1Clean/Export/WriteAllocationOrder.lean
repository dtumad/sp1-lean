import SP1Clean.Export.WriteAllocationQueue
import SP1Clean.Soundness.HintQueueClock

/-! # Physical queue order and allocation ownership

The receiving timestamp strictly orders all HINT handlers and allocating calls together.
Consequently each private walk ends at the outgoing state of its own opening.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteSourceRegistry HostHintQueue WriteAllocation
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : State F}

/-- Original HINT handlers increase the queue clock while preserving its permanent frontier. -/
theorem handler_facts (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (r : HostQueueOrder.Row (p := SP1Prime)) (mem : r ∈ hintHandlerRows w) :
    HostQueueOrder.time (HostQueueOrder.edge r).1 < HostQueueOrder.time (HostQueueOrder.edge r).2 ∧
      (HostQueueOrder.edge r).2.allocated = (HostQueueOrder.edge r).1.allocated := by
  let orig : EnsembleWitness (HostObserved.ensemble image source target final) := supervisor w
  let host := hostWitness orig
  have hc := HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints orig (supervisor_constraints w checked)))
  have c := TransitionView.readIndexedRows_constraints HostQueueOrder.indices
    (fun i => (HostQueueOrder.view (p := SP1Prime) i).component) (HostHintReadLocal.queueTables host)
    (HostHintReadLocal.queueTables_aligned host) (fun t member => hc t (HostHintReadLocal.queueTables_mem host t member)) r mem
  exact HostQueueOrder.checked_edge r.1 r.2 c

attribute [local irreducible] base withSources preprocessing

private theorem mem_enabled {I : TypeMap} [ProvableType I] {t : Table F} {x : I F}
    (member : x ∈ enabledInputs (guardedInputs I t)) :
    ∃ row ∈ t.table, (valueFromOffset (ProvablePair I field) 0 (t.environment row)).1 = x ∧
      (valueFromOffset (ProvablePair I field) 0 (t.environment row)).2 = 1 := by
  obtain ⟨pair,m,rfl⟩ := List.mem_map.mp member
  obtain ⟨physical,active⟩ := List.mem_filter.mp m
  obtain ⟨row,live,rfl⟩ := List.mem_map.mp physical
  exact ⟨row,live,rfl,of_decide_eq_true active⟩

/-- Every enabled physical allocation header has the actual checked chronology and timestamp decomposition. -/
theorem allocation_header_valid (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (r : Open F) (mem : r ∈ (allocationInputs w).1) : r.Valid := by
  let o := slot image source target final 15
  obtain ⟨row,found,equal,active⟩ := mem_enabled (I := Open) (t := o.table w) mem
  have c := o.table_constraints w checked row found
  rw [o.table_component w] at c
  rw [← equal]
  exact (openInput_valid _ c).2 active

private theorem advances (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (op : QueueOperation) (mem : op ∈ queueOperations w) :
    HostQueueOrder.time (queueEdge op).1 < HostQueueOrder.time (queueEdge op).2 := by
  rcases List.mem_append.mp mem with old | call
  · obtain ⟨r,live,rfl⟩ := List.mem_map.mp old
    exact (handler_facts w checked _ live).1
  · obtain ⟨r,live,rfl⟩ := List.mem_map.mp call
    exact (allocation_header_valid w checked _ live).2.2.2.2.2.2.2

/-- Every genuine queue operation lies on a single connected, strictly chronological walk
from the incoming state to the seal. Its outgoing times have no repetitions. -/
theorem native_ordered_queue (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    let start := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) source.host.io.hints
    ∃ path, path.Perm (queueOperations seen) ∧ Walk.IsWalk queueEdge start (finalQueue seen) path ∧
      (path.map fun row => HostQueueOrder.time (queueEdge row).2).Pairwise (· < ·) := by
  classical
  let seen := observed w
  let start := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) source.host.io.hints
  have balanced : RankedGrounding.EndpointBalanced (↑(queueOperations seen)) queueEdge start (finalQueue seen) := by
    simpa only [RankedGrounding.EndpointBalanced,Multiset.map_coe,Multiset.cons_coe,Multiset.coe_eq_coe] using
      native_queue_endpoints w checked fit raw
  obtain ⟨path,walk,exhaustive⟩ := RankedGrounding.exists_exhaustiveTrail_of_endpointBalanced
    (↑(queueOperations seen)) queueEdge HostQueueOrder.time start (finalQueue seen) balanced
    (advances seen ((observed_constraints w).mp checked))
  have ordered := Multiset.coe_eq_coe.mp exhaustive
  exact ⟨path,ordered,walk,RankedGrounding.targetRanks_pairwise_of_isWalk queueEdge HostQueueOrder.time walk
    (fun r m => advances seen ((observed_constraints w).mp checked) r (ordered.mem_iff.mp m))⟩

/-- Two allocating headers can never share the outgoing timestamp on the physical global
queue, irrespective of intervening original HINT operations. -/
theorem native_allocation_clock_unique (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((allocationInputs (observed w)).1.map (fun r => HostQueueOrder.time r.outgoing)).Nodup := by
  obtain ⟨ordered,allOps,_,times⟩ := native_ordered_queue w checked fit raw
  have unique := ((allOps.map (fun r => HostQueueOrder.time (queueEdge r).2)).nodup_iff.mp
    (times.imp Nat.ne_of_lt))
  exact (List.nodup_append.mp (by simpa only [queueOperations,List.map_append,List.map_map,Function.comp_def,queueEdge,
      Sum.elim_inl,Sum.elim_inr] using unique)).2.1

/-- Private allocation walks terminate at the outgoing state of their own physical call.
All authorized counts and all active fresh-node occurrences are retained, even for repeated data. -/
theorem native_matched_allocations (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let ins := allocationInputs (observed w)
    ∃ batches : List (List (Step F)), List.Forall₂ (fun (call : Open F) batch =>
        Walk.IsWalk (fun r : Step F => (r.before,r.after)) call.first call.last batch ∧
        batch.length = Address.toNat call.count) ins.1 batches ∧ batches.flatten.Perm ins.2 := by
  let ins := allocationInputs (observed w)
  have calls := native_allocation_clock_unique w checked fit raw
  obtain ⟨paths,walks,ends,steps⟩ := native_allocation_walks w checked fit raw
  refine ⟨paths.map Prod.fst, List.forall₂_map_right_iff.mpr ?_, ?_⟩
  · apply List.forall₂_iff_zip.mpr
    refine ⟨walks.length_eq,?_⟩
    intro call path pair
    have both := List.of_mem_zip pair
    obtain ⟨walk,len,_,_,high,low⟩ := (List.forall₂_iff_zip.mp walks).2 pair
    obtain ⟨other,member,endEq⟩ := List.mem_map.mp (ends.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) both.2))
    have stamp : HostQueueOrder.time other.outgoing = HostQueueOrder.time call.outgoing := by
      change HostQueueOrder.time other.last.state = _
      rw [endEq]
      simp only [HostQueueOrder.time,high,low]
    have same := List.inj_on_of_nodup_map calls member both.1 stamp
    subst other
    exact ⟨endEq.symm ▸ walk,len⟩
  · simpa only [List.flatMap_def] using steps

end SP1Clean.Export.WriteObservationAssembly
