import SP1Clean.Export.WriteAllocationFrontier
import SP1Clean.Export.WriteAllocationSource
import SP1Clean.Soundness.HintAllocationStore

/-! # The unique persistent node layout of an accepted native segment

Once bytes have been decoded for each physical node, the incoming queue and the actual
sealed frontier determine the complete extended store, including popped nodes.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Fixed identities, physical tails and the sealed frontier leave exactly one persistent
store for any supplied payload function. The word cursors determine the physical payloads. -/
theorem native_store_for_payloads (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (bytes : Step F → Bytes) :
    let base := (ofList source.host.io.hints).1
    let seen := observed w
    ∃! store : Store, Extends base store ∧ WellFormed store ∧
      store.size = Address.toNat (finalQueue seen).allocated ∧
      ∀ r ∈ (allocationInputs seen).2, node? store (Address.toNat r.node.node.pointer) =
        some ⟨bytes r,Address.toNat r.node.node.tail⟩ := by
  let base := (ofList source.host.io.hints).1
  obtain ⟨rows,allRows,ids,terminal⟩ := native_allocation_frontier w checked fit raw
  have sourceSize := (native_initial_frontier w fit raw).2
  rw [sourceSize] at ids terminal
  have valid := (allocation_endpoints w checked fit raw).2
  obtain ⟨extension,wf,size,found⟩ := extendStore_records base rows bytes (ofList_wellFormed _) (fun r m => valid r (allRows.mem_iff.mp m)) ids
  refine ⟨extendStore base rows bytes, ⟨extension,wf,size.trans terminal.symm,fun r m => found r (allRows.mem_iff.mpr m)⟩, ?_⟩
  intro other actual
  exact store_unique base rows bytes ids actual.1 extension (actual.2.2.1.trans terminal) size
    (fun r m => actual.2.2.2 r (allRows.mem_iff.mp m)) found

end SP1Clean.Export.WriteObservationAssembly
