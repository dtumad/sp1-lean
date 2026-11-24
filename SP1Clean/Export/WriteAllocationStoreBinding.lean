import SP1Clean.Export.WriteAllocationStorage
import SP1Clean.Export.HintSnapshotWalk

/-! # Binding dynamic immutable publications to their shared persistent store -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

/-- The runtime word environments of the installed persistent-word table. Zero reader counts
are retained at the semantic level whenever their row activity is one. -/
def allocationWords (w : EnsembleWitness (preprocessing image source target final)) : List (Words.Row F) :=
  enabledInputs (guardedInputs Words.Row ((slot image source target final 18).table w))

/-- The complete persistent queue conclusion includes the full incoming store, every fresh
metadata and word record, and the ordered outgoing hint bytes seen by the physical snapshot. -/
structure PersistentQueue (w : EnsembleWitness (native image source target)) (store : Store) : Prop where
  /-- All incoming nodes survive, including subsequently popped ones. -/
  extension : Extends (ofList source.host.io.hints).1 store
  /-- Every persistent tail points to an earlier identity. -/
  wellFormed : WellFormed store
  /-- The physical seal carries the exact final allocation frontier. -/
  frontier : store.size = Address.toNat (finalQueue (observed w)).allocated
  /-- Every active physical metadata row names its node in this store. -/
  nodes : ∀ r ∈ (allocationInputs (observed w)).2, r.node.node.Binds store
  /-- Every active physical word row names the same store's corresponding padded word. -/
  words : ∀ r ∈ allocationWords (observed w), r.word.Binds store
  /-- Walking the sealed head returns exactly the public target list. -/
  outgoing : Represents store (Address.toNat (finalQueue (observed w)).head) target.host.io.hints

/-- Byte-level decoding of every physical dynamic word gives one persistent store for the
entire segment. The allocation layouts, bounds and public ending queue follow from raw acceptance. -/
theorem persistent_queue_of_decoded_words (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (bytes : Step F → Bytes)
    (lengths : ∀ r ∈ (allocationInputs (observed w)).2, (bytes r).length = Address.toNat r.length)
    (content : ∀ word ∈ allocationWords (observed w), ∃ r ∈ (allocationInputs (observed w)).2,
      word.word ∈ nodeWordRows (p := SP1Prime) (Address.toNat r.node.node.pointer) (bytes r)) :
    ∃ store, PersistentQueue w store := by
  obtain ⟨store,state,_⟩ := native_store_for_payloads w checked fit raw bytes
  obtain ⟨extension,wf,frontier,physical⟩ := state
  have valid := (allocation_endpoints w checked fit raw).2
  have nodes (r) (m : r ∈ (allocationInputs (observed w)).2) : r.node.node.Binds store := by
    refine ⟨_,physical r m,rfl,?_⟩
    rw [length_bits (valid _ m)]
    exact congrArg (BitVec.ofNat 64) (lengths r m).symm
  have words (row) (m : row ∈ allocationWords (observed w)) : row.word.Binds store := by
    obtain ⟨r,mem,word⟩ := content _ m
    exact nodeWordRows_binds (physical r mem) (Address.toNat_lt (valid r mem).2.1.2.2.2.2.1.1) _ word
  refine ⟨store,extension,wf,frontier,nodes,words,?_⟩
  apply outgoing_queue_of_allocations w checked fit raw store extension
  · intro r emitted
    obtain ⟨input,mem,_,rfl⟩ := emitted.enabled
    exact nodes _ mem
  · intro r emitted
    obtain ⟨input,mem,_,rfl⟩ := emitted.enabled
    exact words _ mem

end SP1Clean.Export.WriteObservationAssembly
