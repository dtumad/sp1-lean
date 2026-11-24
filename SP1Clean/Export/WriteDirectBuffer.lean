import SP1Clean.Export.WriteDirectNode
import SP1Clean.Export.WriteGuestLanes

/-! # A whole raw direct WRITE hint from authenticated guest Memory -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem stored_group_lane (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (g : WriteEffects.Group F) (mg : g ∈ allocationGroups (observed w)) (direct : g.previous.sink = 14)
    {node : HintQueue.Node} (found : node? store (Address.toNat g.previous.owner) = some node)
    (j : Fin 8) (small : j.val < g.plan.size.val) :
    BitVec.ofNat 8 g.octets.bytes[(g.plan.first.val + j.val)%8].val =
      (node.bytes[Address.toNat g.previous.position + j.val]?.getD 0) := by
  have retained : g.previous.sink ≠ 0 := by
    intro h
    have impossible := congrArg ZMod.val (direct.symm.trans h)
    rw [show (14 : F).val = 14 by decide,ZMod.val_zero] at impossible
    contradiction
  obtain ⟨side,gate,k,_,position,lanes⟩ := native_placement_block w ok fit raw g mg retained j small
  obtain ⟨r,mr,_,_,block⟩ := native_direct_group w ok fit raw g mg side gate direct
  have pointer := congrArg StreamBlock.reply block
  have nodeAt : node? store (Address.toNat r.word.pointer) = some node := by
    change node? store (Address.toNat r.prior.contents.pointer) = some node
    change r.prior.contents.pointer = g.previous.owner at pointer
    rwa [pointer]
  have index := congrArg StreamBlock.index block
  have bytes := congrArg StreamBlock.bytes block
  change r.payload.bytes = (g.block side).bytes at bytes
  rw [← bytes] at lanes
  have rawByte := Words.Row.stored_lane ((native_word_endpoints w ok fit raw).2 r mr) (stored.words r mr) nodeAt k
  change BitVec.ofNat 8 r.payload.bytes[k].val = (node.bytes[Address.toNat r.direct.index * 8 + k.val]?.getD 0) at rawByte
  rw [index,position] at rawByte
  exact (congrArg (fun x : F => BitVec.ofNat 8 x.val) lanes).trans rawByte

/-- The actual persistent direct node has the specified byte length. Its i-th byte comes
from the original aligned Memory word covering x11+i at the incoming dispatcher clock. -/
def DirectBufferAt (w : EnsembleWitness (native image source target)) (store : Store) (d : Dispatch F) : Prop :=
    ∃ node, node? store (Address.toNat d.pointer) = some node ∧ node.bytes.length = Address.toNat d.length ∧
      ∀ i : Fin node.bytes.length, GuestByteAt w d i.val node.bytes[i.val]

/-- Every byte of the persistent hint created by a genuine direct dispatcher is the
original guest byte at x11 plus its index, read at that dispatcher's incoming clock. The
exact length and pointer come from the physical allocation, including the empty case. -/
theorem native_direct_buffer (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w)) (direct : d.flags.direct = 1) :
    DirectBufferAt w store d := by
  obtain ⟨_,_,_,_,_,_,_,_,_,node,found,length,_⟩ := native_direct_node w ok fit raw stored d md direct
  refine ⟨node,found,length,?_⟩
  have dv := ((native_allocation_tickets w ok fit raw).2 d md).1
  have shape := (direct_shape dv).2 direct
  have owner : d.owner d.flags = d.pointer := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Dispatch.owner,shape,DispatchFlags.hook,threeLimbs,circuit_norm]
  have zero : Address.toNat (d.start d.flags).position = 0 := by
    simp [Dispatch.start,Dispatch.outputPosition,shape,threeLimbs,Address.toNat,circuit_norm]
  intro i
  obtain ⟨g,mg,sink,content,j,small,index,guest⟩ := native_guest_lane w ok fit raw d (allocating_dispatch_active w ok fit raw d md)
    i.val (length ▸ i.isLt)
  have atNode : node? store (Address.toNat g.previous.owner) = some node := by rwa [content,owner]
  have alloc := stored_group_lane w ok fit raw stored g mg (sink.trans ((direct_shape dv).1.mp direct)) atNode j small
  rw [zero,zero_add] at index
  rwa [alloc,index,List.getElem?_eq_getElem i.isLt,Option.getD_some] at guest

end SP1Clean.Export.WriteObservationAssembly
