import SP1Clean.Export.WriteDirectNode
import SP1Clean.Export.WriteGuestOctets
import SP1Clean.Soundness.WritePlacementCoverage

/-! # A whole raw direct WRITE hint from authenticated guest Memory -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem direct_coordinates {d : Dispatch F} (v : d.Valid) (direct : d.flags.direct = 1) :
    Address.toNat (d.start d.flags).position = 0 ∧ Address.toNat (d.finish d.flags).position = Address.toNat d.length ∧
    d.request.header.address.toNat = Address.toNat (d.start d.flags).address + 1 ∧ (d.start d.flags).owner = d.pointer := by
  have shape := (direct_shape v).2 direct
  obtain ⟨_,_,size,base,_,_,_,_,addr,_,finish,_⟩ := v
  have zero : Address.toNat (d.outputPosition d.flags) = 0 := by
    simp [shape,Dispatch.outputPosition,threeLimbs,Address.toNat,circuit_norm]
  refine ⟨zero,?_,addr.2.2,?_⟩
  · have endPos := finish.2.2.2
    change Address.toNat d.endPosition = Address.toNat d.basePosition + Address.toNat d.payloadLength at endPos
    rwa [base,zero,zero_add,size] at endPos
  · apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Dispatch.start,Dispatch.owner,shape,DispatchFlags.hook,threeLimbs,circuit_norm]

private theorem block_index {pos offset j left right : Nat} (offsetEq : offset = pos % 8) (leftEq : left = pos / 8)
    (rightEq : right = left + 1) (small : j < 8) :
    (if offset + j < 8 then left else right) * 8 + (offset + j) % 8 = pos + j := by
  split <;> omega

private theorem stored_group_lane (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (g : WriteEffects.Group F) (mg : g ∈ allocationGroups (observed w)) (direct : g.previous.sink = 14)
    {node : HintQueue.Node} (found : node? store (Address.toNat g.previous.owner) = some node)
    (j : Fin 8) (small : j.val < g.plan.size.val) :
    BitVec.ofNat 8 g.octets.bytes[(g.plan.first.val + j.val)%8].val =
      (node.bytes[Address.toNat g.previous.position + j.val]?.getD 0) := by
  obtain ⟨f,s,o,first,room,offset,plan,lanes⟩ := native_direct_lanes w ok fit raw g mg direct
  have mod : 8 < SP1Prime := by decide
  have firstEq : g.plan.first.val = f := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have sizeEq : g.plan.size.val = s := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have offEq : g.plan.offset.val = o := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  obtain ⟨r,mr,_,ptr,index,bytes⟩ := lanes j (sizeEq ▸ small)
  have coords := (native_group_plan w ok fit raw g mg).1.1
  have advance := coords.2.2.2.2.2.2.2.2.2
  change Address.toNat g.nextBlock = Address.toNat g.firstBlock + Address.toNat (#v[1,0,0] : fields 3 F) at advance
  rw [show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at advance
  have idx := block_index (offEq.symm.trans coords.2.2.2.1) coords.2.2.1 advance j.isLt
  have atPos : Address.toNat r.word.index * 8 + (o+j.val)%8 = Address.toNat g.previous.position + j.val := by
    change Address.toNat r.prior.index * 8 + _ = _
    rw [index,apply_ite Address.toNat]
    exact idx
  have nodeAt : node? store (Address.toNat r.word.pointer) = some node := by
    change node? store (Address.toNat r.prior.contents.pointer) = some node
    rwa [ptr]
  let k : Fin 8 := ⟨(o+j.val)%8,Nat.mod_lt _ (by decide)⟩
  have equal := Words.Row.stored_lane ((native_word_endpoints w ok fit raw).2 r mr) (stored.words r mr) nodeAt k
  change BitVec.ofNat 8 r.payload.bytes[(o+j.val)%8].val = (node.bytes[Address.toNat r.word.index * 8 + (o+j.val)%8]?.getD 0) at equal
  rw [atPos] at equal
  let L (x : Nat) : Fin 8 := ⟨(x+j.val)%8,Nat.mod_lt _ (by decide)⟩
  have same := congrArg (fun x : Nat => g.octets.bytes[L x]) firstEq
  exact (congrArg (fun x : F => BitVec.ofNat 8 x.val) (same.trans bytes)).trans equal

/-- The actual persistent direct node has the specified byte length. Its i-th byte comes
from the original aligned Memory word covering x11+i at the incoming dispatcher clock. -/
def DirectBufferAt (w : EnsembleWitness (native image source target)) (store : Store) (d : Dispatch F) : Prop :=
    ∃ node, node? store (Address.toNat d.pointer) = some node ∧ node.bytes.length = Address.toNat d.length ∧
      ∀ i : Fin node.bytes.length, ∃ s : WriteBuffer.Step F, s.Valid ∧
        WriteProbe.ReadMeaning (rawSource ((appended image source target _).project (observed w))) s.read ∧
        s.read.clock = d.request.header.clock ∧ ∃ lane : Fin 8,
          Address.toNat s.read.key + lane.val = d.request.header.address.toNat + i.val ∧
          s.read.value.toBitVec64.extractLsb' (8 * lane.val) 8 = node.bytes[i.val]

/-- Every byte of the persistent hint created by a genuine direct dispatcher is the
original guest byte at x11 plus its index, read at that dispatcher's incoming clock. The
exact length and pointer come from the physical allocation, including the empty case. -/
theorem native_direct_buffer (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w)) (direct : d.flags.direct = 1) :
    DirectBufferAt w store d := by
  obtain ⟨_,_,_,_,_,_,_,_,_,node,found,length,_⟩ := native_direct_node w ok fit raw stored d md direct
  refine ⟨node,found,length,?_⟩
  obtain ⟨groups,walk,steps⟩ := native_direct_placement w ok fit raw d md direct
  have used (g) (m : g ∈ groups) := placement_step_active _ ((observed_constraints w).mp ok) g (steps g m)
  have dv := ((native_allocation_tickets w ok fit raw).2 d md).1
  obtain ⟨start,finish,address,owner⟩ := direct_coordinates dv direct
  have movement (g) (m : g ∈ groups) : g.Movements := by
    obtain ⟨mg,pos⟩ := used g m
    obtain ⟨valid,f,s,o,_,room,_,plan⟩ := native_group_plan w ok fit raw g mg
    obtain ⟨sample,sampled,_,key,_,_⟩ := native_guest_octets w ok fit raw g mg
    exact Group.movements valid (key ▸ sampled.1) plan room pos
  intro i
  obtain ⟨g,mg,clock,sink,content,j,small,index,placement⟩ := placement_lane walk movement i.val (by rw [start]; omega)
    (by rw [finish,← length]; exact i.isLt)
  have src := (used g mg).1
  obtain ⟨s,sv,read,key,same,decoded⟩ := native_guest_octets w ok fit raw g src
  have gc := (native_group_plan w ok fit raw g src).1.1.1
  have atNode : node? store (Address.toNat g.previous.owner) = some node := by rwa [content,owner]
  have alloc := stored_group_lane w ok fit raw stored g src (sink.trans ((direct_shape dv).1.mp direct)) atNode j small
  have bound := (movement g mg).fits
  let lane : Fin 8 := ⟨g.plan.first.val + j.val,by omega⟩
  refine ⟨s,sv,read,same.trans (gc.symm.trans clock),lane,?_,?_⟩
  · rw [start,Nat.sub_zero,← address] at placement
    change Address.toNat s.read.key + (g.plan.first.val + j.val) = _
    rw [key,← Nat.add_assoc]
    exact placement
  · have block : (g.plan.first.val+j.val)%8 = lane.val := Nat.mod_eq_of_lt lane.isLt
    rw [index,List.getElem?_eq_getElem i.isLt,Option.getD_some] at alloc
    let srcLane : Fin 8 := ⟨(g.plan.first.val+j.val)%8,Nat.mod_lt _ (by decide)⟩
    have sameLane : srcLane = lane := Fin.ext block
    have sameByte := congrArg (fun k : Fin 8 => BitVec.ofNat 8 g.octets.bytes[k].val) sameLane
    exact (decoded lane).2.symm.trans (sameByte.symm.trans alloc)

end SP1Clean.Export.WriteObservationAssembly
