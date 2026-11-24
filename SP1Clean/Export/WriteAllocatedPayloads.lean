import SP1Clean.Export.WriteDirectBuffer
import SP1Clean.Export.WriteAllocationStoreUnique

/-! # All physical allocating WRITE payloads in the unique native queue store -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Raw native acceptance fixes one persistent store for the entire segment. Each
allocating dispatcher in it supplies either the guest bytes at x11 or the complete public
hook return batch at its reply ordinal. This includes zero-length writes and zero-return hooks. -/
theorem native_allocated_payloads (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃! store, PersistentQueue w store ∧ ∀ d ∈ allocatingDispatches (observed w),
      (d.flags.direct = 1 ∧ DirectBufferAt w store d) ∨ (d.flags.hook = 1 ∧ ReturnedBatchAt w store d) := by
  obtain ⟨store,stored,unique⟩ := native_persistent_queue_unique w ok fit raw
  refine ⟨store,⟨stored,?_⟩,fun other h => unique other h.1⟩
  intro d md
  obtain ⟨valid,gate⟩ := (native_allocation_tickets w ok fit raw).2 d md
  rcases valid.allocation_gates.1 with zero | one
  · have direct : d.flags.direct = 1 := by simpa only [zero,add_zero] using gate
    exact Or.inl ⟨direct,native_direct_buffer w ok fit raw stored d md direct⟩
  · exact Or.inr ⟨one,native_hook_batch w ok fit raw stored d md one⟩

end SP1Clean.Export.WriteObservationAssembly
