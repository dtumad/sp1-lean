import SP1Clean.Export.WriteAllocationWalks

/-! # Exact guarded message handoffs in an arbitrary native witness -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- A complete two-slot guarded handoff preserves the multiset of whole enabled messages. -/
theorem guarded_slots_perm {M I J : TypeMap} [ProvableType M] [ProvableType I] [ProvableType J] (ch : Channel F M)
    (seen : EnsembleWitness (preprocessing image source target final)) (a b : Fin 19)
    (registered : ch.toRaw ∈ channels) (separate : ch.toRaw ≠ WriteProbe.readbackChannel.toRaw) (support : selectedSlots source target ch.toRaw = [a,b])
    (push : I F → M F) (pull : J F → M F)
    (produced : ∀ env, (tables source target)[a.val].operations.interactionValuesWith ch.toRaw env =
      let r := valueFromOffset (ProvablePair I field) 0 env; [ch.pushedIfValue r.2 (push r.1)])
    (consumed : ∀ env, (tables source target)[b.val].operations.interactionValuesWith ch.toRaw env =
      let r := valueFromOffset (ProvablePair J field) 0 env; [ch.pulledIfValue r.2 (pull r.1)])
    (left : ∀ r ∈ guardedInputs I ((slot image source target final a).table seen), IsBool r.2)
    (right : ∀ r ∈ guardedInputs J ((slot image source target final b).table seen), IsBool r.2)
    (paid : seen.BalancedChannel ch.toRaw) :
    ((enabledInputs (guardedInputs I ((slot image source target final a).table seen))).map push).Perm
      ((enabledInputs (guardedInputs J ((slot image source target final b).table seen))).map pull) := by
  let s := slot image source target final a
  let t := slot image source target final b
  let xs := guardedInputs I (s.table seen)
  let ys := guardedInputs J (t.table seen)
  have lhs : (s.table seen).interactionsWith ch.toRaw = xs.map (fun r => ch.pushedIfValue r.2 (push r.1)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,xs,guardedInputs,List.flatMap_map,s.table_component seen]
    exact List.flatMap_congr fun row _ => produced _
  have rhs : (t.table seen).interactionsWith ch.toRaw = ys.map (fun r => ch.pulledIfValue r.2 (pull r.1)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,ys,guardedInputs,List.flatMap_map,t.table_component seen]
    exact List.flatMap_congr fun row _ => consumed _
  change BalancedInteractions (seen.interactionsWith ch.toRaw) at paid
  rw [fresh_slots_ledger seen _ registered separate,support] at paid
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at paid
  change BalancedInteractions ((s.table seen).interactionsWith ch.toRaw ++ (t.table seen).interactionsWith ch.toRaw) at paid
  rw [lhs,rhs] at paid
  simpa only [enabledInputs,List.map_map,Function.comp_def] using
    ch.gated_perm_of_balanced xs Prod.snd (fun r => push r.1) ys Prod.snd (fun r => pull r.1) left right paid

/-- Physical row-local validity transfers to the enabled typed inputs, retaining gate facts for all rows. -/
theorem guarded_table_facts {I : TypeMap} [ProvableType I] {t : Table F} {P : I F → Prop}
    (sound : ∀ row ∈ t.table, let x := valueFromOffset (ProvablePair I field) 0 (t.environment row)
      IsBool x.2 ∧ (x.2 = 1 → P x.1)) :
    (∀ x ∈ guardedInputs I t, IsBool x.2) ∧ ∀ x ∈ enabledInputs (guardedInputs I t), P x := by
  constructor
  · intro x m
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp m
    exact (sound row present).1
  · intro x m
    obtain ⟨r,selected,rfl⟩ := List.mem_map.mp m
    obtain ⟨existsRow,on⟩ := List.mem_filter.mp selected
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp existsRow
    exact (sound row present).2 (of_decide_eq_true on)

end SP1Clean.Export.WriteObservationAssembly
