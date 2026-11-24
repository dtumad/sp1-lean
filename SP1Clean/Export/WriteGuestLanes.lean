import SP1Clean.Export.WriteDirectCalls
import SP1Clean.Export.WriteGuestOctets
import SP1Clean.Soundness.WritePlacementCoverage

/-! # The original guest byte and absolute destination position of every WRITE lane -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- One byte equals an extraction at its actual guest address and incoming clock from a
physical original Memory supplier. -/
def GuestByteAt (w : EnsembleWitness (native image source target)) (d : Dispatch F) (i : Nat) (b : BitVec 8) : Prop :=
  ∃ s : WriteBuffer.Step F, s.Valid ∧ WriteProbe.ReadMeaning (rawSource ((appended image source target _).project (observed w))) s.read ∧
    s.read.clock = d.request.header.clock ∧ ∃ lane : Fin 8,
      Address.toNat s.read.key + lane.val = d.request.header.address.toNat + i ∧
        s.read.value.toBitVec64.extractLsb' (8 * lane.val) 8 = b

/-- A byte of any dispatched WRITE selects a real nonempty placement, a valid absolute
destination offset, and the matching guest Memory observation. -/
theorem native_guest_lane (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w))
    (i : Nat) (hi : i < Address.toNat d.length) :
    ∃ g ∈ allocationGroups (observed w), g.previous.sink = d.flags.sink ∧ g.previous.owner = d.owner d.flags ∧
      ∃ j : Fin 8, j.val < g.plan.size.val ∧ Address.toNat g.previous.position + j.val = Address.toNat (d.start d.flags).position + i ∧
        GuestByteAt w d i (BitVec.ofNat 8 g.octets.bytes[(g.plan.first.val + j.val)%8].val) := by
  obtain ⟨groups,walk,steps⟩ := native_dispatch_placement w ok fit raw d md
  have used (g) (m : g ∈ groups) := placement_step_active _ ((observed_constraints w).mp ok) g (steps g m)
  obtain ⟨_,_,size,base,_,_,_,_,addr,_,finish,_⟩ := (physical_dispatch_valid w ok fit raw d md).1
  have endPos := finish.2.2.2
  change Address.toNat d.endPosition = Address.toNat d.basePosition + Address.toNat d.payloadLength at endPos
  rw [base,size] at endPos
  have movement (g) (m : g ∈ groups) : g.Movements := by
    obtain ⟨mg,pos⟩ := used g m
    obtain ⟨valid,f,s,o,_,room,_,plan⟩ := native_group_plan w ok fit raw g mg
    obtain ⟨sample,sampled,_,key,_,_⟩ := native_guest_octets w ok fit raw g mg
    exact Group.movements valid (key ▸ sampled.1) plan room pos
  let basePos := Address.toNat (d.start d.flags).position
  obtain ⟨g,mg,clock,sink,owner,j,small,index,placement⟩ := placement_lane walk movement (basePos + i) (Nat.le_add_right _ _)
    (by change Address.toNat (d.outputPosition d.flags) + i < Address.toNat d.endPosition; omega)
  have src := (used g mg).1
  obtain ⟨s,sv,read,key,same,decoded⟩ := native_guest_octets w ok fit raw g src
  have gc := (native_group_plan w ok fit raw g src).1.1.1
  have bound := (movement g mg).fits
  let lane : Fin 8 := ⟨(g.plan.first.val+j.val)%8,Nat.mod_lt _ (by decide)⟩
  refine ⟨g,src,sink,owner,j,small,index,s,sv,read,same.trans (gc.symm.trans clock),lane,?_,(decoded lane).2.symm⟩
  have before := addr.2.2
  change d.request.header.address.toNat = Address.toNat (d.start d.flags).address + 1 at before
  have guest : Address.toNat g.octets.key + g.plan.first.val + j.val = d.request.header.address.toNat + i := by
    simpa only [basePos,Nat.add_sub_cancel_left,← before] using placement
  change Address.toNat s.read.key + ((g.plan.first.val + j.val)%8) = _
  rw [key,Nat.mod_eq_of_lt (by omega),← Nat.add_assoc]
  exact guest

end SP1Clean.Export.WriteObservationAssembly
