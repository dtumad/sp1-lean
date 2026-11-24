import SP1Clean.Proofs.Operations.QueueAllocationEdges
import SP1Clean.Proofs.Operations.WriteMetadataRows

/-! # The exact guarded dispatch-to-allocator ticket messages -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- One physical dispatch funds its atomic ticket exactly when its row is enabled and the
classified descriptor allocates a direct buffer or calls a hook. -/
def ticketGate (r : Dispatch F × F) : F := r.2 * (r.1.flags.direct+r.1.flags.hook)

private theorem ticket_values (r : Var Dispatch F) (n : Nat) (env : Environment F) :
    ((dispatchMain r).operations n).interactionValuesWith queueEffectChannel.toRaw env =
      let d := ProvableStruct.eval env r
      [queueEffectChannel.pushedIfValue (d.flags.direct+d.flags.hook) (d.ticket d.flags)] := by
  have raw : ((dispatchMain r).operations n).interactionsWith queueEffectChannel.toRaw =
      [(queueEffectChannel.pushedIf (r.flags.direct+r.flags.hook) (r.ticket r.flags)).toRaw] := by
    rw [dispatch_ledger _ _ _ (by simp [queueEffectChannel,Channels.byteChannel,circuit_norm])]
    simp [requestChannel,cursorChannel,recordChannel,queueEffectChannel,positionChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushedIf]
  rcases r with ⟨⟨⟨_,_,_,_⟩,_⟩,⟨_,_,_,_,_⟩,⟨_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_,_,_,_⟩
  simp only [Dispatch.ticket,Dispatch.owner,Dispatch.length,DispatchFlags.hook,threeLimbs,circuit_norm]

/-- The literal signed ticket publication produced by an arbitrary dispatch environment. -/
theorem dispatch_ticket_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Dispatch field) 0 env
    (dispatchComponent (p := SP1Prime)).operations.interactionValuesWith queueEffectChannel.toRaw env =
      [queueEffectChannel.pushedIfValue (ticketGate r) (r.1.ticket r.1.flags)] := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main dispatchCircuit dispatchGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((dispatchMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [ticket_values]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pushedIfValue,Guarded.eval_activity,proj,input,I,eval_varFromOffset_valueFromOffset,ticketGate]

end SP1Clean.WriteEffects

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat WriteEffects
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Every enabled allocator header requests the entire originating ticket, including the
incoming ECALL time and the distinction between direct buffers and returned hooks. -/
theorem open_ticket_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Open field) 0 env
    (openComponent (p := SP1Prime)).operations.interactionValuesWith queueEffectChannel.toRaw env =
      [queueEffectChannel.pulledIfValue r.2 r.1.ticket] := by
  let I := ProvablePair Open field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main openCircuit openSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((openMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((openMain input.1).operations (size I)).interactionsWith queueEffectChannel.toRaw =
        [(queueEffectChannel.pulled input.1.ticket).toRaw] := by
    rw [open_ledger]
    simp [queueEffectChannel,cursorChannel,HostHintQueue.stateChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  have proj (i : Var I F) : eval env i.1.ticket = (eval env i).1.ticket := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,I,eval_varFromOffset_valueFromOffset]

end SP1Clean.WriteAllocation
