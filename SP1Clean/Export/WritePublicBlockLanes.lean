import SP1Clean.Export.WriteGuestLanes

/-! # Exact occupied bytes of fixed public WRITE output and request blocks -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

private theorem key_injective : Function.Injective StreamKey.coordinates := by
  intro k other same
  cases k <;> cases other <;> simp_all [StreamKey.coordinates]

/-- A retained placement to a named public stream or hook request authenticates an occupied
byte of that exact endpoint. It cannot be funded by direct-hint allocations. -/
theorem native_public_group_lane (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (g : WriteEffects.Group F) (mg : g ∈ allocationGroups (observed w))
    (key : StreamKey) (tag : g.previous.sink.val = key.coordinates.1) (owner : Address.toNat g.previous.owner = key.coordinates.2.1)
    (hint : key.coordinates.2.2 = 0) (retained : key.coordinates.1 ≠ 0) (publicTag : key.coordinates.1 ≠ 14)
    (j : Fin 8) (small : j.val < g.plan.size.val) :
    ∃ bytes, key.contents (.fromEndpoints source.host target.host) = some bytes ∧ ∃ i : Fin bytes.length,
      i.val = Address.toNat g.previous.position + j.val ∧ BitVec.ofNat 8 g.octets.bytes[(g.plan.first.val + j.val)%8].val = bytes[i.val] := by
  have used : g.previous.sink ≠ 0 := fun h => retained (tag.symm.trans (h ▸ ZMod.val_zero))
  obtain ⟨side,gate,k,occupied,atIndex,byte⟩ := native_placement_block w ok fit raw g mg used j small
  let b := g.block side
  have fixed : FixedBlock (.fromEndpoints source.host target.host) b := by
    rcases native_block_origin w ok fit raw b (group_block_pull _ _ mg side gate) with fixed | allocated
    · exact fixed
    · obtain ⟨r,_,_,_,equal⟩ := allocated
      have name := congrArg (fun p : StreamBlock F => p.stream.val) equal
      change (14 : F).val = g.previous.sink.val at name
      exact (publicTag (tag.symm.trans (name.symm.trans (by decide)))).elim
  obtain ⟨valid,actual,bytes,index,found,live,block⟩ := fixed
  have fields := encodeBlock_fields (p := SP1Prime) _ valid found live
  rw [← block] at fields
  obtain ⟨stream,reply,zero,idx,usedBytes,lanes⟩ := fields
  have name : actual = key := by
    apply key_injective
    apply Prod.ext
    · exact stream.symm.trans tag
    · exact Prod.ext (reply.symm.trans owner) (zero.symm.trans (hint ▸ (by decide : Address.toNat (#v[0,0,0] : fields 3 F) = 0)))
  subst actual
  let i := Address.toNat g.previous.position + j.val
  have absIndex : index * 8 + k.val = i := idx ▸ atIndex
  have inside : i < bytes.length := by
    change k.val < b.used.val at occupied
    rw [usedBytes] at occupied
    omega
  refine ⟨bytes,found,⟨i,inside⟩,rfl,?_⟩
  have read := lanes k
  rw [absIndex,List.getElem?_eq_getElem inside,Option.getD_some] at read
  rw [byte]
  exact (congrArg (BitVec.ofNat 8) read).trans (BitVec.ofNat_toNat 8 _)

end SP1Clean.Export.WriteObservationAssembly
