import SP1Clean.Export.WritePlacementWalks
import SP1Clean.Proofs.Operations.WriteChronologyRows
import SP1Clean.Soundness.WriteReplyChronology

/-! # One exhaustive stream cursor walk over every raw WRITE dispatcher -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
open scoped Classical
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem registered : (cursorChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 11) rfl

private theorem public_start (w : EnsembleWitness (assembly image source target final)) :
    let ch := (cursorChannel (p := SP1Prime)).toRaw
    (w.interactionsWith ch).Perm ([cursorChannel.pushedValue (initialCursor source.clock)] ++ (observed w).interactionsWith ch) := by
  let ch := (cursorChannel (p := SP1Prime)).toRaw
  let checker := WriteEffects.checker (p := SP1Prime) source.host target.host
  let cursors := withCursors image source target final
  let prev := checker.project (ens := cursors) w
  have inside : ch ∈ cursors.channels := protocol_installed image source target final _ registered
  have ledger : prev.interactionsWith ch = w.interactionsWith ch :=
    checker.project_interactions _ ch (fun eq => checker.channel_not_mem cursors (eq ▸ inside))
  change (w.interactionsWith ch).Perm _
  rw [← ledger]
  change ((withCursors image source target final).verifierOperations.interactionValuesWith ch w.data.publicEnvironment ++
    w.toTables.interactionsWith ch).Perm ([cursorChannel.pushedValue (initialCursor source.clock)] ++
    ((preprocessing image source target final).verifierOperations.interactionValuesWith ch w.data.publicEnvironment ++ w.toTables.interactionsWith ch))
  rw [withCursors_ledger]
  have onlyStart : ([cursorChannel.pushedValue (initialCursor source.clock),closeChannel.pulledValue (finalCursor target.clock (.fromEndpoints source.host target.host))].filter
      (fun e : Interaction F => decide (e.channel = ch))) = [cursorChannel.pushedValue (initialCursor source.clock)] := by
    simp [Channel.pushedValue,Channel.pulledValue,closeChannel,cursorChannel,ch,Channel.toRaw]
  rw [onlyStart,← List.append_assoc]
  exact (List.perm_append_comm ..).append_right _

private theorem stream_funding (w : EnsembleWitness (assembly image source target final)) (fit : w.InteractionsFit .logUp)
    (raw : w.Balanced .logUp) :
    let seen := observed w
    let d := slot image source target final 8
    let c := slot image source target final 14
    let stop := finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)
    BalancedInteractions ([cursorChannel.pushedValue (initialCursor source.clock)] ++ (guardedInputs Dispatch (d.table seen)).flatMap dispatchCursors ++
      (c.table seen).table.map (fun r => cursorChannel.pulledValue ((valueFromOffset CloseInput 0 ((c.table seen).environment r)).source stop))) := by
  let ch := (cursorChannel (p := SP1Prime)).toRaw
  let seen := observed w
  let d : TableSlot (preprocessing image source target final).tables dispatchComponent := slot image source target final 8
  let c : TableSlot (preprocessing image source target final).tables (closeComponent source target) := slot image source target final 14
  let stop := finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)
  have funded := w.balancedChannels_of_balanced fit raw ch (by
    unfold assembly withCursors; exact List.mem_append_left _ (protocol_installed image source target final _ registered))
  have paid := BalancedInteractions.of_perm funded (public_start w)
  have useOnly : selectedSlots source target ch = [8,14] := rfl
  have parts := fresh_slots_ledger seen ch registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
  rw [useOnly] at parts
  have dl : (d.table seen).interactionsWith ch = (guardedInputs Dispatch (d.table seen)).flatMap dispatchCursors := by
    simp only [Table.interactionsWith,guardedInputs,List.flatMap_map,d.table_component seen]
    exact List.flatMap_congr fun r _ => dispatch_cursors_at _
  have cl : (c.table seen).interactionsWith ch = (c.table seen).table.map (fun r =>
      cursorChannel.pulledValue ((valueFromOffset CloseInput 0 ((c.table seen).environment r)).source stop)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,c.table_component seen]
    exact List.flatMap_congr fun r _ => close_cursor_at source target _
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at parts
  change (seen.interactionsWith ch) = (d.table seen).interactionsWith ch ++ (c.table seen).interactionsWith ch at parts
  change BalancedInteractions ([cursorChannel.pushedValue (initialCursor source.clock)] ++ seen.interactionsWith ch) at paid
  rw [parts,dl,cl,← List.append_assoc] at paid
  exact paid

private theorem close_once (start : StreamCursor F) (ds : List (Dispatch F × F)) (ends : List (StreamCursor F))
    (bits : ∀ r ∈ ds, IsBool r.2)
    (paid : BalancedInteractions ([cursorChannel.pushedValue start] ++ ds.flatMap dispatchCursors ++ ends.map cursorChannel.pulledValue)) :
    ∃ stop, ends = [stop] ∧
      (start :: (enabledInputs ds).map (fun d => d.next d.flags)).Perm (stop :: (enabledInputs ds).map Dispatch.previous) := by
  let edge := fun r : Dispatch F × F => (r.1.previous,r.1.next r.1.flags)
  let rows := ds.filter fun r => decide (r.2 = 1)
  have blocked : ((ends.map cursorChannel.pulledValue).filter (fun i => decide (i.mult ≠ 0))) = ends.map cursorChannel.pulledValue := by
    apply List.filter_eq_self.mpr
    intro i m
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp m
    exact decide_eq_true one_ne_zero
  have live := paid.filter_nonzero
  have opened : ([cursorChannel.pushedValue start].filter (fun i => decide (i.mult ≠ 0))) = [cursorChannel.pushedValue start] := by
    apply List.filter_eq_self.mpr
    intro i m
    obtain rfl := List.mem_singleton.mp m
    exact decide_eq_true one_ne_zero
  rw [List.filter_append,List.filter_append,opened,blocked] at live
  change BalancedInteractions (([cursorChannel.pushedValue start] ++
    ((ds.flatMap fun r => [cursorChannel.pulledIfValue r.2 (edge r).1,cursorChannel.pushedIfValue r.2 (edge r).2]).filter _)) ++ ends.map cursorChannel.pulledValue) at live
  rw [cursorChannel.gatedPairs_filter_nonzero ds Prod.snd edge bits] at live
  have grouped := ((cursorChannel.pairedLedger_perm rows edge).append_left [cursorChannel.pushedValue start]).append_right (ends.map cursorChannel.pulledValue)
  have pure := BalancedInteractions.of_perm live grouped
  let produce := start :: rows.map (fun r => (edge r).2)
  let consume := rows.map (fun r => (edge r).1) ++ ends
  have msgs := (cursorChannel.balanced_unit_iff produce consume).mp (by
    simpa only [produce,consume,List.map_cons,List.map_map,Function.comp_def,List.map_append,List.singleton_append,List.cons_append,List.append_assoc,List.nil_append] using pure)
  have len := msgs.length_eq
  simp only [produce,consume,List.length_cons,List.length_map,List.length_append] at len
  obtain ⟨stop,rfl⟩ := List.length_eq_one_iff.mp (show ends.length = 1 by omega)
  refine ⟨stop,rfl,?_⟩
  simpa only [enabledInputs,List.map_map,Function.comp_def,produce,rows,edge,List.singleton_append] using
    (msgs.trans (List.perm_append_comm (l₁ := rows.map (fun r => (edge r).1)) (l₂ := [stop])))

/-- Every accepted native WRITE appears once in a chronological list, from the public
incoming counters to the physical terminal that receives the fixed endpoint counters. -/
theorem native_dispatch_walk (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃ prior : fields 3 F, ∃ path : List (Dispatch F), path.Perm (physicalDispatches (observed w)) ∧
      Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) (initialCursor source.clock)
        ({finalCursor target.clock (.fromEndpoints source.host target.host) with clock := prior}) path := by
  classical
  let seen := observed w
  let ds := guardedInputs Dispatch ((slot image source target final 8).table seen)
  let t := (slot image source target final 14).table seen
  let stop := finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)
  let finish := fun row => (valueFromOffset CloseInput 0 (t.environment row)).source stop
  let edge := fun d : Dispatch F => (d.previous,d.next d.flags)
  let rows := physicalDispatches seen
  have funds : BalancedInteractions ([cursorChannel.pushedValue (initialCursor source.clock)] ++ ds.flatMap dispatchCursors ++
      (t.table.map finish).map cursorChannel.pulledValue) := by
    simpa only [List.map_map,Function.comp_def] using stream_funding w fit raw
  obtain ⟨last,ends,counts⟩ := close_once _ ds _ (fun r m => (native_dispatch_input_facts w ok fit raw r m).1) funds
  have appears : last ∈ t.table.map finish := ends ▸ List.mem_cons_self
  obtain ⟨terminal,_,rfl⟩ := List.mem_map.mp appears
  have balance : RankedGrounding.EndpointBalanced (rows : Multiset (Dispatch F)) edge (initialCursor source.clock) (finish terminal) := by
    simp only [RankedGrounding.EndpointBalanced,Multiset.map_coe,Multiset.cons_coe,Multiset.coe_eq_coe]
    exact counts
  have increases (d) (m : d ∈ rows) : Address.toNat (edge d).1.clock < Address.toNat (edge d).2.clock := by
    obtain ⟨r,kept,rfl⟩ := List.mem_map.mp m
    obtain ⟨active,flag⟩ := List.mem_filter.mp kept
    have v := (native_dispatch_input_facts w ok fit raw r active).2 (of_decide_eq_true flag)
    obtain ⟨before,after⟩ := v.stream_time
    change Address.toNat r.1.previous.clock < Address.toNat (r.1.next r.1.flags).clock
    omega
  obtain ⟨path,walk,exhaustive⟩ := RankedGrounding.exists_exhaustiveTrail_of_endpointBalanced (rows : Multiset (Dispatch F)) edge
    (fun c => Address.toNat c.clock) _ _ balance increases
  exact ⟨_,path,Multiset.coe_eq_coe.mp exhaustive,walk⟩

/-- The public verifier enforces the full host boundary comparison and the natural
bounds on the fixed stream records in every raw balanced native witness. -/
theorem native_stream_boundary (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) : boundarySpec source.host target.host := by
  let checker := WriteEffects.checker (p := SP1Prime) source.host target.host
  have owned := ((checker.project_balanced_iff (ens := withCursors image source target final) w).mp
    (w.balancedChannels_of_balanced fit raw)).2
  exact (checker_checks source.host target.host w.publicInput w.data).mp owned

private theorem endpoint_replies (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    Address.toNat (finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)).replies =
      (WriteStreams.fromEndpoints source.host target.host).hooks.length :=
  Address.toNat_ofNat _ (hooks_lt_of_inventory (native_stream_boundary w fit raw).2)

/-- The entire physical dispatch list can be sorted by the actual incoming clocks. At
every position its reply ordinal is exactly the number of preceding classified hooks.
The terminal counters are fixed even for a segment with no WRITE. -/
theorem native_dispatch_chronology (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃ prior : fields 3 F, ∃ path : List (Dispatch F), path.Perm (physicalDispatches (observed w)) ∧
      Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) (initialCursor source.clock)
        ({finalCursor target.clock (.fromEndpoints source.host target.host) with clock := prior}) path ∧
      (path.map (fun d => Address.toNat d.request.header.clock)).Pairwise (· < ·) ∧
      path.countP (fun d => decide (d.flags.hook = 1)) = (WriteStreams.fromEndpoints source.host target.host).hooks.length ∧
      ∀ i : Fin path.length, Address.toNat path[i.val].previous.replies =
        (path.take i.val).countP (fun d => decide (d.flags.hook = 1)) := by
  obtain ⟨prior,path,all,walk⟩ := native_dispatch_walk w ok fit raw
  have valid (d) (m : d ∈ path) : d.Valid := by
    obtain ⟨r,kept,rfl⟩ := List.mem_map.mp (all.mem_iff.mp m)
    obtain ⟨active,on⟩ := List.mem_filter.mp kept
    exact (native_dispatch_input_facts w ok fit raw r active).2 (of_decide_eq_true on)
  have zero : Address.toNat (initialCursor (p := SP1Prime) source.clock).replies = 0 := by
    change Address.toNat (Address.ofNat (p := SP1Prime) 0) = 0
    decide
  refine ⟨prior,path,all,walk,dispatch_walk_order walk valid,?_,fun i => ?_⟩
  · have total := dispatch_walk_total walk valid
    change Address.toNat (finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)).replies = _ at total
    rwa [endpoint_replies w fit raw,zero,zero_add,eq_comm] at total
  · simpa only [zero,zero_add] using dispatch_walk_ordinals walk valid i

end SP1Clean.Export.WriteObservationAssembly
