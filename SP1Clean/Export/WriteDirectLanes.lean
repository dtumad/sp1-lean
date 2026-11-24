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

/-- Every selected direct-placement guest octet belongs to an actually occupied allocation
word of the same fresh pointer and block index, even when the group crosses a block boundary. -/
theorem native_direct_lanes (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (g : WriteEffects.Group F) (mem : g ∈ allocationGroups (observed w))
    (direct : g.previous.sink = 14) :
    ∃ first size offset : Nat, first < 8 ∧ first+size ≤ 8 ∧ offset < 8 ∧ g.plan = .ofNat first size offset ∧
      ∀ j : Fin 8, j.val < size → ∃ r ∈ allocationWords (observed w), r.directGate = 1 ∧
        r.prior.contents.pointer = g.previous.owner ∧ r.prior.index = (if offset+j.val < 8 then g.firstBlock else g.nextBlock) ∧
        g.octets.bytes[(first+j.val)%8] = r.payload.bytes[(offset+j.val)%8] := by
  obtain ⟨v,first,size,offset,small,room,off,plan⟩ := native_group_plan w checked fit raw g mem
  refine ⟨first,size,offset,small,room,off,plan,?_⟩
  have sink : g.previous.sink ≠ 0 := by
    intro z
    have bad := congrArg ZMod.val (direct.symm.trans z)
    rw [show (14 : F).val = 14 by decide,ZMod.val_zero] at bad
    contradiction
  have used : g.ignored = 0 := v.2.2.1.trans (ite_eq_right sink)
  intro j lane
  have equal := v.2.1.atLane plan small off j lane (fun h => zero_ne_one (used.symm.trans h))
  by_cases left : offset+j.val < 8
  · have gate : g.leftGate = 1 := by simp [Group.leftGate,used,plan,SlicePlan.ofNat,show size ≠ 0 by omega]
    obtain ⟨r,member,active,_,value⟩ := native_direct_group w checked fit raw g mem false gate direct
    have ptr := congrArg StreamBlock.reply value
    have pos := congrArg StreamBlock.index value
    have bytes := congrArg StreamBlock.bytes value
    change r.payload.bytes = g.left at bytes
    exact ⟨r,member,active,ptr,by rw [ite_eq_left left]; exact pos,by rwa [ite_eq_left left,← bytes] at equal⟩
  · have gate : g.rightGate = 1 := by simp [Group.rightGate,used,plan,SlicePlan.ofNat,show 8 < size+offset by omega]
    obtain ⟨r,member,active,_,value⟩ := native_direct_group w checked fit raw g mem true gate direct
    have ptr := congrArg StreamBlock.reply value
    have pos := congrArg StreamBlock.index value
    have bytes := congrArg StreamBlock.bytes value
    change r.payload.bytes = g.right at bytes
    exact ⟨r,member,active,ptr,by rw [ite_eq_right left]; exact pos,by rwa [ite_eq_right left,← bytes] at equal⟩

end SP1Clean.Export.WriteObservationAssembly
