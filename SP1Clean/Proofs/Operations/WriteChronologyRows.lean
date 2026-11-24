import SP1Clean.Proofs.Operations.WriteMetadataRows
import SP1Clean.Native.Operations.WriteCursorBoundary

/-! # Physical dispatcher and terminal stream cursor transitions -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Both signed stream occurrences of every actual dispatcher, at its original activity. -/
def dispatchCursors (r : Dispatch F × F) : List (Interaction F) :=
  [cursorChannel.pulledIfValue r.2 r.1.previous,cursorChannel.pushedIfValue r.2 (r.1.next r.1.flags)]

private theorem dispatch_cursors (r : Var Dispatch F) (n : Nat) (env : Environment F) :
    ((dispatchMain r).operations n).interactionValuesWith cursorChannel.toRaw env =
      let d := ProvableStruct.eval env r
      [cursorChannel.pulledValue d.previous,cursorChannel.pushedValue (d.next d.flags)] := by
  have raw : ((dispatchMain r).operations n).interactionsWith cursorChannel.toRaw =
      [(cursorChannel.pulled r.previous).toRaw,(cursorChannel.pushed (r.next r.flags)).toRaw] := by
    rw [dispatch_ledger _ _ _ (by simp [cursorChannel,Channels.byteChannel,circuit_norm])]
    simp [requestChannel,cursorChannel,recordChannel,queueEffectChannel,positionChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushed,Channel.eval_pulled]
  rcases r with ⟨⟨⟨_,_,_,_⟩,_⟩,⟨_,_,_,_,_⟩,⟨_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_,_,_,_⟩
  simp only [Dispatch.next,DispatchFlags.hook,threeLimbs,circuit_norm]

/-- A guarded physical dispatcher consumes its previous stream cursor and advances it to its own next state. -/
theorem dispatch_cursors_at (env : Environment F) :
    (dispatchComponent (p := SP1Prime)).operations.interactionValuesWith cursorChannel.toRaw env =
      dispatchCursors (valueFromOffset (ProvablePair Dispatch field) 0 env) := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main dispatchCircuit dispatchGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((dispatchMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [dispatch_cursors]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pushedValue,Channel.pulledValue,Channel.pushedIfValue,Channel.pulledIfValue,
    mul_one,Guarded.eval_activity,proj,input,I,eval_varFromOffset_valueFromOffset,dispatchCursors]

/-- The real closing row consumes its own prior clock with the outgoing endpoint counters. -/
theorem close_cursor_at (source target : ExecutionSnapshot) (env : Environment F) :
    let r := valueFromOffset CloseInput 0 env
    let stop := finalCursor target.clock (.fromEndpoints source.host target.host)
    (closeComponent source target).operations.interactionValuesWith cursorChannel.toRaw env =
      [cursorChannel.pulledValue (r.source stop)] := by
  let stop := finalCursor (p := SP1Prime) target.clock (.fromEndpoints source.host target.host)
  let input := varFromOffset CloseInput (F := F) 0
  have sum (x : Var AddressSum.Inputs F) (off : Nat) :
      FlatOperation.interactions (AddressSum.circuit.toSubcircuit off x).ops.toFlat = [] := by
    rw [FormalAssertion.toSubcircuit_interactions]
    exact AddressSum.interactions x off
  have raw : (closeComponent (p := SP1Prime) source target).operations.interactions =
      [(cursorChannel.pulled (input.source (const stop))).toRaw,(closeChannel.pushedIf input.count (const stop)).toRaw] := by
    rw [Component.interactions_eq]
    change ((closeMain stop input).operations (size CloseInput)).interactions = _
    simp only [closeMain,circuit_norm,sum,List.nil_append]
  have decode (i : Var CloseInput F) (c : Var StreamCursor F) : eval env (i.source c) = (eval env i).source (eval env c) := by
    rcases i with ⟨_,_,_,_⟩
    rcases c with ⟨_,_,_,_,_⟩
    simp only [CloseInput.source,circuit_norm]
  rw [Operations.interactionValuesWith_eq_filter,Operations.interactionValues,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.eval_pushedIf,decode,ProvableType.eval_const,input,eval_varFromOffset_valueFromOffset]
  simp [Channel.pulledValue,Channel.pushedIfValue,cursorChannel,closeChannel,Channel.toRaw,stop]

end SP1Clean.WriteEffects
