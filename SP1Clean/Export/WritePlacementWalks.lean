import SP1Clean.Export.WriteHookCallBuffers
import SP1Clean.Export.WriteDirectLanes
import SP1Clean.Proofs.Operations.WritePlacementEdges

/-! # Exhaustive placement walks from the actual WRITE dispatchers -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- All enabled physical dispatchers, including ignored writes and zero-length buffers. -/
def physicalDispatches (w : EnsembleWitness (preprocessing image source target final)) : List (Dispatch F) :=
  enabledInputs (guardedInputs Dispatch ((slot image source target final 8).table w))

private def nonempty (r : WriteEffects.Group F × F) : F := r.2 * r.1.plan.nonempty

/-- The physical position transitions which consume actual guest bytes. Empty windows
have no position transition while retaining their original plan and octet requests. -/
def placementSteps (w : EnsembleWitness (preprocessing image source target final)) : List (WriteEffects.Group F) :=
  ((guardedInputs WriteEffects.Group ((slot image source target final 9).table w)).filter
    (fun r => decide (nonempty r = 1))).map Prod.fst

private theorem position_registered : (positionChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 9) rfl

private theorem position_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (positionChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 8).table w).interactionsWith ch ++
      ((slot image source target final 9).table w).interactionsWith ch := by
  let ch := (positionChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [8,9] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch position_registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- Original enabled and padding dispatcher inputs carry their checked activity/semantic contract. -/
theorem native_dispatch_input_facts (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∀ x ∈ guardedInputs Dispatch ((slot image source target final 8).table (observed w)), IsBool x.2 ∧ (x.2 = 1 → x.1.Valid) := by
  let seen := observed w
  let h := slot image source target final 8
  have ok := (observed_constraints w).mp checked
  have bytes := (byte_guarantees seen ok (observed_byte_balance w fit raw)).2 _ (h.table_mem seen)
  intro x mem
  obtain ⟨row,m,rfl⟩ := List.mem_map.mp mem
  have val := h.table_constraints seen ok row m
  have b := bytes row m
  rw [h.table_component seen] at val b
  exact dispatch_valid_at _ val b

private theorem placements_checked (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints) :
    ∀ r ∈ guardedInputs WriteEffects.Group ((slot image source target final 9).table w), IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  intro r mem
  obtain ⟨row,m,rfl⟩ := List.mem_map.mp mem
  let h := slot image source target final 9
  have c := h.table_constraints w ok row m
  rw [h.table_component w] at c
  have v := guarded_group_valid (varFromOffset (ProvablePair WriteEffects.Group field) 0) _ _ ((Component.constraintsHold_iff _).mp c)
  rwa [eval_varFromOffset_valueFromOffset] at v

private theorem step_origin (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints)
    (g : WriteEffects.Group F) (mem : g ∈ placementSteps w) : g ∈ allocationGroups w ∧ g.plan.nonempty = 1 := by
  obtain ⟨r,kept,rfl⟩ := List.mem_map.mp mem
  obtain ⟨present,selected⟩ := List.mem_filter.mp kept
  have one : nonempty r = 1 := of_decide_eq_true selected
  have flag := (placements_checked w ok r present).1
  have act : r.2 = 1 := flag.resolve_left (fun off => zero_ne_one (by simpa only [nonempty,off,zero_mul] using one))
  exact ⟨List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨present,decide_eq_true act⟩,rfl⟩,by simpa only [nonempty,act,one_mul] using one⟩

private theorem increased (g : WriteEffects.Group F) (v : g.Valid) {first size offset : Nat}
    (pf : g.plan = .ofNat first size offset) (maxSize : first+size ≤ 8) (present : g.plan.nonempty = 1) :
    Address.toNat g.previous.position < Address.toNat g.next.position := by
  have nonzero : size ≠ 0 := by
    intro z
    have bad : (0 : F) = 1 := by simpa only [pf,SlicePlan.ofNat,z,ite_true] using present
    exact zero_ne_one bad
  have hp : 8 < SP1Prime := by decide
  have sz : g.plan.size.val = size := by rw [pf]; exact ZMod.val_natCast_of_lt (by omega)
  have advance := v.1.2.2.2.2.2.1.2.2.2
  change Address.toNat g.next.position = Address.toNat g.previous.position + Address.toNat (#v[g.plan.size,0,0] : fields 3 F) at advance
  have encoded : Address.toNat (#v[g.plan.size,0,0] : fields 3 F) = size := by simp [Address.toNat,circuit_norm,sz]
  rw [advance,encoded]
  exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero nonzero)

/-- Every active dispatcher opens a complete placement walk for its byte window. The
partition uses every nonempty physical position row and every closing occurrence exactly
once and rules out disconnected groups by strictly increasing stream positions. -/
theorem native_placement_walks (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    ∃ paths : List (List (WriteEffects.Group F) × Placement F),
      List.Forall₂ (fun d path => Walk.IsWalk (fun g : WriteEffects.Group F => (g.previous,g.next)) (d.start d.flags) path.2 path.1)
        (physicalDispatches seen) paths ∧ (paths.map Prod.snd).Perm ((physicalDispatches seen).map fun d => d.finish d.flags) ∧
        (paths.flatMap Prod.fst).Perm (placementSteps seen) := by
  let seen := observed w
  let ch := (positionChannel (p := SP1Prime)).toRaw
  let d := slot image source target final 8
  let h := slot image source target final 9
  let ds := guardedInputs Dispatch (d.table seen)
  let hs := guardedInputs WriteEffects.Group (h.table seen)
  have checks := (observed_constraints w).mp ok
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ position_registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [position_ledger] at paid
  have a : (d.table seen).interactionsWith ch = ds.flatMap dispatchPositions := by
    simp only [Table.interactionsWith,ds,guardedInputs,List.flatMap_map,d.table_component seen]
    exact List.flatMap_congr fun row _ => dispatch_positions_at _
  have b : (h.table seen).interactionsWith ch = hs.flatMap groupPositions := by
    simp only [Table.interactionsWith,hs,guardedInputs,List.flatMap_map,h.table_component seen]
    exact List.flatMap_congr fun row _ => group_positions_at _
  change BalancedInteractions ((d.table seen).interactionsWith ch ++ (h.table seen).interactionsWith ch) at paid
  rw [a,b] at paid
  have bits (r) (m : r ∈ hs) : IsBool (nonempty r) := by
    obtain ⟨bit,v⟩ := placements_checked seen checks r m
    rcases bit with off | on
    · simp [nonempty,off,IsBool]
    · simpa only [nonempty,on,one_mul] using (v on).2.2.2.1
  have ends := gated_walk_endpoints positionChannel ds Prod.snd (fun x => x.1.start x.1.flags) (fun x => x.1.finish x.1.flags)
    hs nonempty (fun x => x.1.previous) (fun x => x.1.next) (fun r m => (native_dispatch_input_facts w ok fit raw r m).1) bits paid
  let edge := fun g : WriteEffects.Group F => (g.previous,g.next)
  let starts := (physicalDispatches seen).map (fun d => d.start d.flags)
  let stops := (physicalDispatches seen).map (fun d => d.finish d.flags)
  let rows := placementSteps seen
  have paired : (starts ++ rows.map (fun r => (edge r).2)).Perm (stops ++ rows.map (fun r => (edge r).1)) := by
    simp only [starts,stops,rows,edge,physicalDispatches,enabledInputs,placementSteps,List.map_map,Function.comp_def]
    exact ends
  have grows (g) (m : g ∈ rows) : Address.toNat g.previous.position < Address.toNat g.next.position := by
    obtain ⟨present,flag⟩ := step_origin seen checks g m
    obtain ⟨v,f,s,o,_,bound,_,plan⟩ := native_group_plan w ok fit raw g present
    exact increased g v plan bound flag
  obtain ⟨paths,walk,term,used⟩ := Walk.partition_ranked edge (fun p => Address.toNat p.position) starts stops rows
    (by simpa only [Multiset.map_coe,Multiset.coe_add,Multiset.coe_eq_coe] using paired) grows
  exact ⟨paths,List.forall₂_map_left_iff.mp walk,Multiset.coe_eq_coe.mp term,Multiset.coe_eq_coe.mp used⟩

end SP1Clean.Export.WriteObservationAssembly
