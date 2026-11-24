import SP1Clean.Export.WriteReturnedBuffers
import SP1Clean.Proofs.Operations.WriteAllocationTickets

/-! # Actual dispatch tickets and their ordered allocations in raw native witnesses -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem ticket_registered : (queueEffectChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 12) rfl

/-- Every allocating ticket is issued on a physical dispatcher row and consumed on a
physical queue allocator header, preserving padding occurrences at both sites. -/
theorem allocation_ticket_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (queueEffectChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 8).table w).interactionsWith ch ++
      ((slot image source target final 15).table w).interactionsWith ch := by
  let ch := (queueEffectChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [8,15] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch ticket_registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- Actual allocating dispatcher inputs, selected by their physical activity and route. -/
def allocatingDispatches (w : EnsembleWitness (preprocessing image source target final)) : List (Dispatch F) :=
  ((guardedInputs Dispatch ((slot image source target final 8).table w)).filter
    (fun r => decide (ticketGate r = 1))).map Prod.fst

private theorem checked_gate {r : Dispatch F × F} (v : IsBool r.2 ∧ (r.2 = 1 → r.1.Valid)) : IsBool (ticketGate r) := by
  rcases v.1 with off | on
  · simp [ticketGate,off,IsBool]
  · simpa only [ticketGate,on,one_mul] using (v.2 on).allocation_gates.2

/-- The actual allocating dispatch rows and active queue headers agree as complete ticket
multisets. Every dispatch supplying such a ticket is enabled and satisfies the real classifier
and all chronological address, length and clock constraints. -/
theorem native_allocation_tickets (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((allocatingDispatches (observed w)).map (fun d => d.ticket d.flags)).Perm
      ((allocationInputs (observed w)).1.map Open.ticket) ∧
    ∀ d ∈ allocatingDispatches (observed w), d.Valid ∧ d.flags.direct + d.flags.hook = 1 := by
  let seen := observed w
  let ch := (queueEffectChannel (p := SP1Prime)).toRaw
  let d : TableSlot (preprocessing image source target final).tables dispatchComponent := slot image source target final 8
  let h : TableSlot (preprocessing image source target final).tables openComponent := slot image source target final 15
  let ds := guardedInputs Dispatch (d.table seen)
  let hs := guardedInputs Open (h.table seen)
  have ok := (observed_constraints w).mp checked
  have bytes := (byte_guarantees seen ok (observed_byte_balance w fit raw)).2 _ (d.table_mem seen)
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ ticket_registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [allocation_ticket_ledger] at paid
  have produces : (d.table seen).interactionsWith ch = ds.map (fun r => queueEffectChannel.pushedIfValue (ticketGate r) (r.1.ticket r.1.flags)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,ds,guardedInputs,List.flatMap_map,d.table_component seen]
    exact List.flatMap_congr fun row _ => dispatch_ticket_at _
  have consumes : (h.table seen).interactionsWith ch = hs.map (fun r => queueEffectChannel.pulledIfValue r.2 r.1.ticket) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,hs,guardedInputs,List.flatMap_map,h.table_component seen]
    exact List.flatMap_congr fun row _ => open_ticket_at _
  change BalancedInteractions ((d.table seen).interactionsWith ch ++ (h.table seen).interactionsWith ch) at paid
  rw [produces,consumes] at paid
  have valid : ∀ r ∈ ds, IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
    intro r m
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp m
    have atRow := d.table_constraints seen ok row present
    have atByte := bytes row present
    rw [d.table_component seen] at atRow atByte
    exact dispatch_valid_at _ atRow atByte
  have heads : ∀ r ∈ hs, IsBool r.2 := by
    intro r m
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp m
    have atRow := h.table_constraints seen ok row present
    rw [h.table_component seen] at atRow
    exact (openInput_valid _ atRow).1
  have perm := queueEffectChannel.gated_perm_of_balanced ds ticketGate (fun r => r.1.ticket r.1.flags) hs Prod.snd
    (fun r => r.1.ticket) (fun r m => checked_gate (valid r m)) heads paid
  refine ⟨?_,?_⟩
  · simp only [allocatingDispatches,allocationInputs,enabledInputs,List.map_map,Function.comp_def]
    exact perm
  intro row mem
  obtain ⟨r,kept,rfl⟩ := List.mem_map.mp mem
  obtain ⟨present,selected⟩ := List.mem_filter.mp kept
  have one := of_decide_eq_true selected
  change ticketGate r = 1 at one
  obtain ⟨binary,v⟩ := valid r present
  have enabled : r.2 = 1 := binary.resolve_left (fun off => zero_ne_one (by simpa only [ticketGate,off,zero_mul] using one))
  exact ⟨v enabled,by simpa only [ticketGate,enabled,one_mul] using one⟩

end SP1Clean.Export.WriteObservationAssembly
