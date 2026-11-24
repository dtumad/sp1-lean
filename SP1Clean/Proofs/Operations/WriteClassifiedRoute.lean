import SP1Clean.Native.Operations.WriteDispatch
import SP1Clean.Native.Operations.WriteEffects
import SP1Clean.FormalModel.Contracts.WriteStreamPositions
import SP1Clean.Math.SP1Field

/-! # Physical flags and coordinates of released WRITE destinations -/

namespace SP1Clean.WriteEffects
open Semantics
private abbrev F := ZMod SP1Prime

/-- The five explicit equality flags for a semantic route. -/
def routeFlags : WriteRoute → DispatchFlags F
  | .ignored => ⟨1,0,0,0,0⟩
  | .stdout => ⟨0,1,0,0,0⟩
  | .stderr => ⟨0,0,1,0,0⟩
  | .publicValues => ⟨0,0,0,1,0⟩
  | .hint => ⟨0,0,0,0,1⟩
  | .hook _ => ⟨0,0,0,0,0⟩

/-- The released descriptor always chooses precisely its native one-hot flags. -/
theorem semantic_flags (fd : BitVec 64) :
    flagsFor ((WriteRoute.ofDescriptor fd).tag : F) = routeFlags (WriteRoute.ofDescriptor fd) := by
  unfold WriteRoute.ofDescriptor
  split_ifs with _ _ _ _ hooks
  all_goals try decide
  simp only [hookDescriptors, List.mem_cons, List.not_mem_nil, or_false] at hooks
  rcases hooks with h|h|h|h|h|h|h <;> rw [h] <;> decide

private theorem tag_lt (fd : BitVec 64) : (WriteRoute.ofDescriptor fd).tag < SP1Prime := by
  unfold WriteRoute.ofDescriptor
  split_ifs with _ _ _ _ hooks
  all_goals try decide
  simp only [hookDescriptors,List.mem_cons,List.not_mem_nil,or_false] at hooks
  rcases hooks with h|h|h|h|h|h|h <;> rw [h] <;> decide

/-- Recover the semantic route from the original full guest file descriptor. -/
def Dispatch.route (d : Dispatch F) := WriteRoute.ofDescriptor d.request.header.descriptor.toBitVec64

/-- The original released descriptor chooses its natural route tag without field reduction. -/
theorem Dispatch.tag_val {d : Dispatch F} (classified : d.request.Valid) : d.request.route.val = d.route.tag := by
  rw [classified.2,ZMod.val_natCast_of_lt (tag_lt _)]
  rfl

/-- The full x12 word has exactly the natural value of the dispatch length columns. -/
theorem Dispatch.Valid.guest_length {d : Dispatch F} (v : d.Valid) : d.request.header.length.toNat = Address.toNat d.length := by
  rw [Word.toNat_def,v.2.1]
  simp [Dispatch.length,Address.toNat,circuit_norm]

/-- The classified packet and chronological dispatch enforce the same released route. -/
theorem Dispatch.Valid.route_flags {d : Dispatch F} (v : d.Valid) (classified : d.request.Valid) :
    d.flags = routeFlags d.route := by
  rw [v.1,classified.2]
  exact semantic_flags _

private theorem repack (v : fields 3 F) : #v[v[0],v[1],v[2]] = v := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

private theorem copy_limbs (v : fields 3 F) : threeLimbs (fun i => v[i.val]) = v := repack v

private theorem zero_limbs : Address.toNat (threeLimbs (fun _ => (0 : F))) = 0 := by decide

private theorem zero_index (i : Fin 3) : (threeLimbs (fun _ => (0 : F)))[i.val] = 0 := by
  rcases i with ⟨i,h⟩
  interval_cases i <;> rfl

private theorem count_selection (d : Dispatch F) (route : WriteRoute)
    (advance : Address.toNat d.nextCounter =
      Address.toNat (d.oldCounter (routeFlags route)) + Address.toNat (d.increment (routeFlags route))) :
    StreamCounts.ofCursor (d.next (routeFlags route)) = (StreamCounts.ofCursor d.previous).record route (Address.toNat d.length) := by
  cases route
  all_goals
    exact (by
      simp [routeFlags,StreamCounts.record,StreamCounts.ofCursor,Dispatch.next,DispatchFlags.hook,
        Dispatch.oldCounter,Dispatch.outputPosition,Dispatch.increment,copy_limbs,repack,zero_index,
        show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at advance ⊢
      all_goals exact advance)

/-- All four natural cursor counters advance by the semantic effect of this real
descriptor and its observed length. Address-sum constraints prevent field wraparound. -/
theorem Dispatch.Valid.stream_counts {d : Dispatch F} (v : d.Valid) (classified : d.request.Valid) :
    StreamCounts.ofCursor (d.next d.flags) = (StreamCounts.ofCursor d.previous).record d.route (Address.toNat d.length) := by
  have shape := v.route_flags classified
  obtain ⟨_,_,_,_,before,delta,_,_,_,_,_,total⟩ := v
  have advance := total.2.2.2
  change Address.toNat d.nextCounter = Address.toNat d.baseCounter + Address.toNat d.delta at advance
  rw [before,delta,shape] at advance
  rw [shape]
  exact count_selection d d.route advance

private theorem key_selection (d : Dispatch F) (route : WriteRoute) {key : StreamKey}
    (selected : destinationKey route (Address.toNat d.previous.replies) = some key) :
    Address.toNat (d.start (routeFlags route)).position = (StreamCounts.ofCursor d.previous).offset route ∧
      (routeFlags route).sink.val = key.coordinates.1 ∧ Address.toNat (d.owner (routeFlags route)) = key.coordinates.2.1 ∧
      key.coordinates.2.2 = 0 ∧ key.coordinates.1 ≠ 0 ∧ key.coordinates.1 ≠ 14 := by
  cases route <;> simp only [destinationKey,Option.some.injEq,reduceCtorEq] at selected
  all_goals subst key
  all_goals
    exact (by
      simp [routeFlags,StreamCounts.offset,StreamCounts.ofCursor,Dispatch.start,Dispatch.owner,DispatchFlags.sink,
        Dispatch.outputPosition,DispatchFlags.hook,StreamKey.coordinates,copy_limbs,zero_limbs]
      all_goals decide)

/-- The actual placement uses the classified output prefix length, or zero for a fresh
hook request, at the owner's exact reply ordinal. -/
theorem Dispatch.Valid.public_coordinates {d : Dispatch F} (v : d.Valid) (classified : d.request.Valid)
    {key : StreamKey} (selected : destinationKey d.route (Address.toNat d.previous.replies) = some key) :
    let counts := StreamCounts.ofCursor d.previous
    Address.toNat (d.start d.flags).position = counts.offset d.route ∧
      d.flags.sink.val = key.coordinates.1 ∧ Address.toNat (d.owner d.flags) = key.coordinates.2.1 ∧
      key.coordinates.2.2 = 0 ∧ key.coordinates.1 ≠ 0 ∧ key.coordinates.1 ≠ 14 := by
  rw [v.route_flags classified]
  exact key_selection d d.route selected

end SP1Clean.WriteEffects
