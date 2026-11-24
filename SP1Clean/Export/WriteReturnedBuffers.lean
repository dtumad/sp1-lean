import SP1Clean.Export.WriteBlockOrigins
import SP1Clean.Export.WriteAllocationMetadata
import SP1Clean.Soundness.AllocationPayloadRead

/-! # Whole returned hook buffers authenticated by the native WRITE allocation tables -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem returned_reply (n : Step F) (hook : n.direct = 0) : n.contents.reply = n.reply := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Step.contents,scale,hook,circuit_norm]

/-- The physical word partition contains one complete walk for each actual node. Its
members are all enabled rows of the installed immutable-word table. -/
theorem node_word_walk (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (n : Step F) (mem : n ∈ (allocationInputs (observed w)).2) :
    ∃ path, Walk.IsWalk Words.wordEdge (some (Words.start n.contents)) none path ∧
      ∀ r ∈ path, r ∈ allocationWords (observed w) := by
  obtain ⟨paths,paired,used⟩ := native_allocation_word_walks w ok fit raw
  have appears : n ∈ (((allocationInputs (observed w)).2).zip paths).map Prod.fst := by
    rw [List.map_fst_zip paired.length_eq.le]; exact mem
  obtain ⟨⟨n',path⟩,both,e⟩ := List.mem_map.mp appears
  change n' = n at e
  subst n'
  exact ⟨path,(List.forall₂_iff_zip.mp paired).2 both,
    fun r h => used.mem_iff.mp (List.mem_flatten.mpr ⟨path,(List.of_mem_zip both).2,h⟩)⟩

private theorem empty_lanes {r : Words.Row F} (v : r.Valid) (empty : Address.toNat r.prior.remaining = 0)
    (bytes : Bytes) (i : Nat) (pastEnd : bytes.length ≤ i*8) (j : Fin 8) :
    r.payload.bytes[j].val = (bytes[i*8+j.val]?.getD 0).toNat := by
  have mask := v.bounds.2.2.2 j
  rw [empty] at mask
  simp only [Nat.min_zero,Nat.not_lt_zero,ite_false] at mask
  have zero := (v.2.1 j).2.2.2 mask
  rw [zero,List.getElem?_eq_none (by omega),Option.getD_none]
  rfl

/-- Every actual hook node in the shared persistent store contains exactly the returned
buffer at its public reply and hint ordinals, with its allocated tail. This includes empty
buffers and nodes that have already been popped at the final snapshot. -/
theorem native_returned_buffer (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (n : Step F) (mn : n ∈ (allocationInputs (observed w)).2) (hook : n.direct = 0) :
    ∃ bytes, (StreamKey.returned (Address.toNat n.reply) (Address.toNat n.index)).contents
      (.fromEndpoints source.host target.host) = some bytes ∧
      node? store (Address.toNat n.node.node.pointer) = some ⟨bytes,Address.toNat n.node.node.tail⟩ := by
  obtain ⟨bytes,publicBytes,count⟩ := native_returned_length w ok fit raw n mn hook
  obtain ⟨path,walk,physical⟩ := node_word_walk w ok fit raw n mn
  have valid (r) (m : r ∈ path) := (native_word_endpoints w ok fit raw).2 r (physical r m)
  refine ⟨bytes,publicBytes,read_payload store n ((allocation_endpoints w ok fit raw).2 n mn) walk
    (stored.nodes n mn) valid (fun r m => stored.words r (physical r m)) bytes count ?_⟩
  obtain ⟨_,positions⟩ := Words.walk_positions n.contents path walk valid
  intro i
  dsimp only
  intro j
  let r := path[i.val]
  have inPath : r ∈ path := List.getElem_mem i.isLt
  obtain ⟨v,owner,idx,remaining⟩ := positions i
  change r.prior.contents = n.contents at owner
  change Address.toNat r.prior.index = i.val at idx
  change Address.toNat r.prior.remaining = Address.toNat n.length - (8 * i.val) at remaining
  by_cases live : i.val*8 < bytes.length
  · have positive : 0 < Address.toNat r.prior.remaining := by rw [remaining,← count]; omega
    have active := v.bounds.2.2.2 (0 : Fin 8)
    have occupied : (0 : Nat) < min 8 (Address.toNat r.prior.remaining) := lt_min (by decide) positive
    change r.payload.mask[0] = (if 0 < min 8 (Address.toNat r.prior.remaining) then (1 : F) else 0) at active
    rw [ite_eq_left occupied] at active
    have gate : r.hookGate = 1 := by simp only [Words.Row.hookGate,owner,Step.contents,hook,sub_zero,one_mul]; exact active
    obtain ⟨b,found,_,_,lanes⟩ := native_returned_bytes w ok fit raw r (physical r inPath) gate
    rw [owner,returned_reply n hook] at found
    change (StreamKey.returned (Address.toNat n.reply) (Address.toNat n.index)).contents _ = some b at found
    obtain rfl : b = bytes := Option.some.inj (found.symm.trans publicBytes)
    simpa only [idx] using lanes j
  · have empty : Address.toNat r.prior.remaining = 0 := by rw [remaining,← count]; omega
    exact empty_lanes v empty bytes i.val (Nat.le_of_not_gt live) j

end SP1Clean.Export.WriteObservationAssembly
