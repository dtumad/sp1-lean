import SP1Clean.Export.WriteBlockOrigins
import SP1Clean.Proofs.Operations.WritePlacementPlans

/-! # Actual guest lanes matched to immutable direct-hint blocks -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem registered : (sliceChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 13) rfl

private theorem plan_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (sliceChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = [((slot image source target final 9).table w),((slot image source target final 13).table w)].flatMap
      (·.interactionsWith ch) := by
  let ch := (sliceChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [9,13] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

private theorem plan_not_push (p : SlicePlan F) {a : F} (binary : IsBool a) :
    ¬(sliceChannel.pulledIfValue a p).Push := by
  intro push
  rcases binary with rfl | rfl
  · exact push.1 rfl
  · exact push.2 rfl rfl

private theorem group_facts (t : Table F) (installed : t.component = groupComponent) (ok : t.Constraints)
    {row} (m : row ∈ t.table) :
    let r := valueFromOffset (ProvablePair WriteEffects.Group field) 0 (t.environment row)
    IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  have h := ok row m
  rw [installed] at h
  have fact := guarded_group_valid (varFromOffset (ProvablePair WriteEffects.Group field) 0) _ _ ((Component.constraintsHold_iff _).mp h)
  rwa [eval_varFromOffset_valueFromOffset] at fact

/-- The full physical plan request selects one legal pair of guest and destination windows
and the actual enabled placement satisfies its semantic byte and coordinate relations. -/
theorem native_group_plan (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (g : WriteEffects.Group F) (m : g ∈ allocationGroups (observed w)) :
    g.Valid ∧ ∃ first size offset : Nat, first < 8 ∧ first+size ≤ 8 ∧ offset < 8 ∧ g.plan = .ofNat first size offset := by
  let seen := observed w
  let h : TableSlot (preprocessing image source target final).tables groupComponent := slot image source target final 9
  let t := h.table seen
  let ch := (sliceChannel (p := SP1Prime)).toRaw
  have ok := (observed_constraints w).mp checked
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [plan_ledger] at paid
  obtain ⟨x,kept,same⟩ := List.mem_map.mp m
  obtain ⟨physical,one⟩ := List.mem_filter.mp kept
  obtain ⟨row,mem,found⟩ := List.mem_map.mp physical
  let value := valueFromOffset (ProvablePair WriteEffects.Group field) 0 (t.environment row)
  change value = x at found
  subst x
  change value.1 = g at same
  subst g
  have on : value.2 = 1 := of_decide_eq_true one
  refine ⟨(group_facts t (h.table_component seen) (h.table_constraints seen ok) mem).2 on,?_⟩
  refine authenticated_pull_of_tables _ sliceChannel (fun p => ∃ first size offset : Nat, first < 8 ∧ first+size ≤ 8 ∧ offset < 8 ∧ p = .ofNat first size offset) ?_ paid value.1.plan ?_
  · intro table belongs
    rcases List.mem_cons.mp belongs with rfl | last
    · change t.Authenticates sliceChannel _
      intro env present i emitted push
      have flag := (group_facts t (h.table_component seen) (h.table_constraints seen ok) present).1
      change i ∈ (h.table seen).component.operations.interactionValuesWith sliceChannel.toRaw (t.environment env) at emitted
      rw [h.table_component seen,group_plan_at] at emitted
      obtain rfl := List.mem_singleton.mp emitted
      exact (plan_not_push _ flag push).elim
    · obtain rfl := List.mem_singleton.mp last
      let p := slot image source target final 13
      exact plan_authenticates (p.table seen) (p.table_component seen) (p.table_constraints seen ok)
  · apply List.mem_flatMap.mpr
    refine ⟨t,List.mem_cons_self,List.mem_flatMap.mpr ⟨row,mem,?_⟩⟩
    change _ ∈ (h.table seen).component.operations.interactionValuesWith sliceChannel.toRaw (t.environment row)
    rw [h.table_component seen,group_plan_at]
    apply List.mem_singleton.mpr
    change sliceChannel.pulledValue _ = sliceChannel.pulledIfValue value.2 _
    rw [on]; rfl

/-- Every selected lane of a retained group lies inside the declared occupied extent of
one genuine pulled block. Its absolute position is preserved across either block boundary. -/
theorem native_placement_block (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (g : WriteEffects.Group F) (mg : g ∈ allocationGroups (observed w))
    (retained : g.previous.sink ≠ 0) (j : Fin 8) (live : j.val < g.plan.size.val) :
    ∃ side : Bool, (if side then g.rightGate else g.leftGate) = 1 ∧ ∃ k : Fin 8, k.val < (g.block side).used.val ∧
      Address.toNat (g.block side).index * 8 + k.val = Address.toNat g.previous.position + j.val ∧
      g.octets.bytes[(g.plan.first.val + j.val)%8] = (g.block side).bytes[k] := by
  obtain ⟨v,f,s,o,small,room,off,plan⟩ := native_group_plan w checked fit raw g mg
  have modulus : 16 < SP1Prime := by decide
  have firstEq : g.plan.first.val = f := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have sizeEq : g.plan.size.val = s := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have offEq : g.plan.offset.val = o := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have used : g.ignored = 0 := v.2.2.1.trans (ite_eq_right retained)
  have lanes := v.2.1.atLane plan small off j (sizeEq ▸ live) (fun h => zero_ne_one (used.symm.trans h))
  let src (a : Nat) : Fin 8 := ⟨(a+j.val)%8,Nat.mod_lt _ (by decide)⟩
  have field := congrArg (fun a : Nat => g.octets.bytes[src a]) firstEq
  let k := src o
  have offset := offEq.symm.trans v.1.2.2.2.1
  have base := v.1.2.2.1
  have extents := v.2.2.2.2.2
  by_cases left : o + j.val < 8
  · have gate : g.leftGate = 1 := by simp [Group.leftGate,used,plan,SlicePlan.ofNat,show s ≠ 0 by omega]
    have extent := extents.2.2.2.2.1 gate
    have decoded : g.plan.firstExtent.val = min 8 (s+o) := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
    refine ⟨false,gate,k,?_,?_,field.trans (by rwa [ite_eq_left left] at lanes)⟩
    · change (o+j.val)%8 < g.leftSize.val
      omega
    · change Address.toNat g.firstBlock * 8 + (o+j.val)%8 = _
      omega
  · have gate : g.rightGate = 1 := by simp [Group.rightGate,used,plan,SlicePlan.ofNat,show 8 < s+o by omega]
    have extent := extents.2.2.2.2.2 gate
    have decoded : g.plan.secondExtent.val = s+o-8 := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
    have advance := v.1.2.2.2.2.2.2.2.2.2
    change Address.toNat g.nextBlock = Address.toNat g.firstBlock + Address.toNat (#v[1,0,0] : fields 3 F) at advance
    rw [show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at advance
    refine ⟨true,gate,k,?_,?_,field.trans (by rwa [ite_eq_right left] at lanes)⟩
    · change (o+j.val)%8 < g.rightSize.val
      omega
    · change Address.toNat g.nextBlock * 8 + (o+j.val)%8 = _
      omega

end SP1Clean.Export.WriteObservationAssembly
