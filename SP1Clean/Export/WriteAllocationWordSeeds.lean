import SP1Clean.Export.WriteAllocationWalks
import SP1Clean.Proofs.Completeness.WriteAllocationTableHandoff

/-! # Exactly one physical word walk is seeded by every fresh persistent node -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics WriteAllocation WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

/-- Complete physical word-walk seeds, including their source metadata, pointer and byte count. -/
def allocationSeeds (w : EnsembleWitness (preprocessing image source target final)) : List (Contents F) :=
  enabledInputs (guardedInputs Contents ((slot image source target final 17).table w))

private theorem contents_registered : (contentsChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 17) rfl

/-- Signed contents traffic comes from exactly the node and seed slots, retaining padding. -/
theorem allocation_contents_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (contentsChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 16).table w).interactionsWith ch ++
      ((slot image source target final 17).table w).interactionsWith ch := by
  let ch := (contentsChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [16,17] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch contents_registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- Every fresh node starts exactly one word walk and every active word seed is funded by
one of the actual nodes, regardless of its metadata reader count or length. -/
theorem native_word_seeds (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((allocationInputs (observed w)).2.map Step.contents).Perm (allocationSeeds (observed w)) := by
  let seen := observed w
  let ch := (contentsChannel (p := SP1Prime)).toRaw
  let s := slot image source target final 16
  let h := slot image source target final 17
  let steps := guardedInputs Step (s.table seen)
  let heads := guardedInputs Contents (h.table seen)
  have c := (observed_constraints w).mp checked
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ contents_registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [allocation_contents_ledger] at paid
  have produces : (s.table seen).interactionsWith ch = steps.map (fun r => contentsChannel.pushedIfValue r.2 r.1.contents) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,steps,guardedInputs,List.flatMap_map,s.table_component seen]
    exact List.flatMap_congr fun row _ => stepInput_contents _
  have consumes : (h.table seen).interactionsWith ch = heads.map (fun r => contentsChannel.pulledIfValue r.2 r.1) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,heads,guardedInputs,List.flatMap_map,h.table_component seen]
    exact List.flatMap_congr fun row _ => seedInput_contents _
  change BalancedInteractions ((s.table seen).interactionsWith ch ++ (h.table seen).interactionsWith ch) at paid
  rw [produces,consumes] at paid
  have stepGate : ∀ r ∈ steps, IsBool r.2 := by
    intro r m
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp m
    have v := s.table_constraints seen c row mem
    rw [s.table_component seen] at v
    have bit := Guarded.activity_of_constraints stepCircuit stepSupported
      (varFromOffset (ProvablePair Step field) 0) _ _ ((Component.constraintsHold_iff _).mp v)
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at bit
  have seedGate : ∀ r ∈ heads, IsBool r.2 := by
    intro r m
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp m
    have v := h.table_constraints seen c row mem
    rw [h.table_component seen] at v
    have bit := Guarded.activity_of_constraints Words.seedCircuit Words.seedSupported
      (varFromOffset (ProvablePair Contents field) 0) _ _ ((Component.constraintsHold_iff _).mp v)
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at bit
  have authorized := contentsChannel.gated_perm_of_balanced steps Prod.snd (fun r => r.1.contents) heads Prod.snd Prod.fst
    stepGate seedGate paid
  simpa only [allocationInputs,allocationSeeds,enabledInputs,List.map_map,Function.comp_def,steps,heads,s,h,seen] using authorized

end SP1Clean.Export.WriteObservationAssembly
