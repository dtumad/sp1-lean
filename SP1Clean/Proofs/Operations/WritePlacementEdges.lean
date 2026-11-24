import SP1Clean.Proofs.Operations.WriteAllocationTickets
import SP1Clean.Proofs.Operations.WritePlacementPlans

/-! # Physical start, finish and group transitions of the WRITE placement cursor -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- One signed start and finish per guarded physical dispatcher. -/
def dispatchPositions (r : Dispatch F × F) : List (Interaction F) :=
  [positionChannel.pushedIfValue r.2 (r.1.start r.1.flags),positionChannel.pulledIfValue r.2 (r.1.finish r.1.flags)]

/-- Nonempty groups, including ignored writes, receive their current position and advance
by their selected window. Every other row retains two zero-count occurrences. -/
def groupPositions (r : Group F × F) : List (Interaction F) :=
  [positionChannel.pulledIfValue (r.2*r.1.plan.nonempty) r.1.previous,positionChannel.pushedIfValue (r.2*r.1.plan.nonempty) r.1.next]

private theorem dispatch_positions (r : Var Dispatch F) (n : Nat) (env : Environment F) :
    ((dispatchMain r).operations n).interactionValuesWith positionChannel.toRaw env =
      let d := ProvableStruct.eval env r
      [positionChannel.pushedValue (d.start d.flags),positionChannel.pulledValue (d.finish d.flags)] := by
  have raw : ((dispatchMain r).operations n).interactionsWith positionChannel.toRaw =
      [(positionChannel.pushed (r.start r.flags)).toRaw,(positionChannel.pulled (r.finish r.flags)).toRaw] := by
    rw [dispatch_ledger _ _ _ (by simp [positionChannel,Channels.byteChannel,circuit_norm])]
    simp [requestChannel,cursorChannel,recordChannel,queueEffectChannel,positionChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushed,Channel.eval_pulled]
  rcases r with ⟨⟨⟨_,_,_,_⟩,_⟩,⟨_,_,_,_,_⟩,⟨_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_,_,_,_⟩
  simp only [Dispatch.start,Dispatch.finish,Dispatch.owner,Dispatch.outputPosition,DispatchFlags.sink,DispatchFlags.hook,threeLimbs,circuit_norm]

/-- The literal start and end position messages on an arbitrary physical dispatcher. -/
theorem dispatch_positions_at (env : Environment F) :
    (dispatchComponent (p := SP1Prime)).operations.interactionValuesWith positionChannel.toRaw env =
      dispatchPositions (valueFromOffset (ProvablePair Dispatch field) 0 env) := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main dispatchCircuit dispatchGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((dispatchMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [dispatch_positions]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pushedValue,Channel.pulledValue,Channel.pushedIfValue,Channel.pulledIfValue,
    mul_one,Guarded.eval_activity,proj,input,I,eval_varFromOffset_valueFromOffset,dispatchPositions]

private theorem group_positions (r : Var Group F) (n : Nat) (env : Environment F) :
    ((groupMain r).operations n).interactionValuesWith positionChannel.toRaw env =
      let g := ProvableStruct.eval env r
      [positionChannel.pulledIfValue g.plan.nonempty g.previous,positionChannel.pushedIfValue g.plan.nonempty g.next] := by
  have raw : ((groupMain r).operations n).interactionsWith positionChannel.toRaw =
      [(positionChannel.pulledIf r.plan.nonempty r.previous).toRaw,(positionChannel.pushedIf r.plan.nonempty r.next).toRaw] := by
    rw [Operations.interactionsWith,group_ledger]
    simp [octetsChannel,sliceChannel,positionChannel,blockChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulledIf,Channel.eval_pushedIf]
  rcases r with ⟨⟨_,_,_⟩,⟨_,_,_,_,_⟩,⟨_,_,_,_,_,_,_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_⟩
  simp only [Group.next,Address.offset,circuit_norm]

/-- Both actual position occurrences of a physical grouped row, at the exact nonempty guard. -/
theorem group_positions_at (env : Environment F) :
    (groupComponent (p := SP1Prime)).operations.interactionValuesWith positionChannel.toRaw env =
      groupPositions (valueFromOffset (ProvablePair Group field) 0 env) := by
  let I := ProvablePair Group field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main groupCircuit groupGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((groupMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [group_positions]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pulledIfValue,Channel.pushedIfValue,Guarded.eval_activity,proj,input,I,
    eval_varFromOffset_valueFromOffset,groupPositions]

end SP1Clean.WriteEffects
