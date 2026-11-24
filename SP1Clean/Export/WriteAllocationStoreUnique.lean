import SP1Clean.Export.WriteAllocationPersistentQueue

/-! # Uniqueness of the full persistent store of an accepted native segment -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- The full persistent store is unique even for popped or zero-reader dynamic nodes. The
original store fixes every old slot. Physical metadata and complete word walks fix every
fresh slot, including its true natural byte length. -/
theorem native_persistent_queue_unique (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) : ∃! store, PersistentQueue w store := by
  obtain ⟨a,ha⟩ := native_persistent_queue w checked fit raw
  refine ⟨a,ha,?_⟩
  intro b hb
  let nodes := (allocationInputs (observed w)).2
  obtain ⟨paths,paired,used⟩ := native_allocation_word_walks w checked fit raw
  have same (n : Step F) (m : n ∈ nodes) :
      node? a (Address.toNat n.node.node.pointer) = node? b (Address.toNat n.node.node.pointer) := by
    have appears : n ∈ (nodes.zip paths).map Prod.fst := by rw [List.map_fst_zip paired.length_eq.le]; exact m
    obtain ⟨⟨n',path⟩,both,e⟩ := List.mem_map.mp appears
    change n' = n at e
    subst n'
    have physical (r) (member : r ∈ path) : r ∈ allocationWords (observed w) :=
      used.mem_iff.mp (List.mem_flatten.mpr ⟨path,(List.of_mem_zip both).2,member⟩)
    exact Words.walk_determines_node n.contents n.node.node rfl ((List.forall₂_iff_zip.mp paired).2 both)
      (fun r h => (native_word_endpoints w checked fit raw).2 r (physical r h)) (ha.nodes n m) (hb.nodes n m)
      (fun r h => ⟨ha.words r (physical r h),hb.words r (physical r h)⟩)
  let bytes := fun n : Step F => ((node? a (Address.toNat n.node.node.pointer)).getD default).bytes
  have stored (n : Step F) (m : n ∈ nodes) :
      node? a (Address.toNat n.node.node.pointer) = some ⟨bytes n,Address.toNat n.node.node.tail⟩ := by
    obtain ⟨node,found,tail,_⟩ := ha.nodes n m
    cases node
    simp only [bytes,found,Option.getD_some,tail]
  obtain ⟨rows,allRows,ids,size⟩ := native_allocation_frontier w checked fit raw
  have sourceSize := (native_initial_frontier w fit raw).2
  rw [sourceSize] at ids size
  exact store_unique _ rows bytes ids hb.extension ha.extension (hb.frontier.trans size) (ha.frontier.trans size)
    (fun r mem => (same _ (allRows.mem_iff.mp mem)).symm.trans (stored _ (allRows.mem_iff.mp mem)))
    (fun r mem => stored _ (allRows.mem_iff.mp mem))

end SP1Clean.Export.WriteObservationAssembly
