import SP1Clean.Export.WriteDispatchWalk
import SP1Clean.Export.WriteDispatchOrigin
import SP1Clean.Export.WriteDirectBuffer
import SP1Clean.Export.WriteAllocationStoreUnique

/-! # All physical allocating WRITE payloads in the unique native queue store -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteEffects
attribute [local instance 2000] FiniteField.instDecidableEq
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Raw native acceptance fixes one persistent store and an exhaustive chronological WRITE
tape. Every dispatcher has a genuine CPU call and original x12 observation. Direct writes
store the guest bytes at x11, and each hook supplies exactly the next authenticated reply
and its returned buffers. The whole tape exhausts the supplied replies, including calls
with no returned hints. -/
theorem native_allocated_payloads (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃! store, PersistentQueue w store ∧ ∃ path : List (Dispatch F), path.Perm (physicalDispatches (observed w)) ∧
      (path.map (fun d => Address.toNat d.request.header.clock)).Pairwise (· < ·) ∧
      path.countP (fun d => decide (d.flags.hook = 1)) = (WriteStreams.fromEndpoints source.host target.host).hooks.length ∧
      ∀ i : Fin path.length, let d := path[i.val]
        DispatchOrigin w d ∧ Address.toNat d.previous.replies = (path.take i.val).countP (fun r => decide (r.flags.hook = 1)) ∧
          (d.flags.direct = 1 → DirectBufferAt w store d) ∧ (d.flags.hook = 1 → ReturnedBatchAt w store d) := by
  obtain ⟨store,stored,unique⟩ := native_persistent_queue_unique w ok fit raw
  obtain ⟨_,path,all,_,ordered,total,ordinals⟩ := native_dispatch_chronology w ok fit raw
  refine ⟨store,⟨stored,path,all,ordered,total,?_⟩,fun other h => unique other h.1⟩
  intro i
  let d := path[i.val]
  have md : d ∈ physicalDispatches (observed w) := all.mem_iff.mp (List.getElem_mem i.isLt)
  obtain ⟨valid,allocated⟩ := physical_dispatch_valid w ok fit raw d md
  refine ⟨native_dispatch_origin w ok fit raw d md,ordinals i,?_,?_⟩
  · intro direct
    have gate : d.flags.direct + d.flags.hook = 1 := by rw [(direct_shape valid).2 direct]; simp [DispatchFlags.hook]
    exact native_direct_buffer w ok fit raw stored d (allocated gate) direct
  · intro hook
    have gate : d.flags.direct + d.flags.hook = 1 := by rw [valid.hook_flags hook]; simp [DispatchFlags.hook]
    exact native_hook_batch w ok fit raw stored d (allocated gate) hook

end SP1Clean.Export.WriteObservationAssembly
