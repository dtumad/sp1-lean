import SP1Clean.Proofs.Operations.WriteMetadataRows
import SP1Clean.Proofs.Operations.WriteEffects

/-! # Guarded classification and dispatch of full native WRITE headers -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- A physical classifier consumes the complete input packet header. -/
theorem request_header_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Request field) 0 env
    (requestComponent (p := SP1Prime)).operations.interactionValuesWith WriteBuffer.effectHeaderChannel.toRaw env =
      [WriteBuffer.effectHeaderChannel.pulledIfValue r.2 r.1.header] := by
  let I := ProvablePair Request field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main requestCircuit requestGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [WriteBuffer.effectHeaderChannel.pulledIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1.header]
  rw [Guarded.main_interactionValuesWith]
  change (((requestMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((requestMain input.1).operations (size I)).interactionsWith WriteBuffer.effectHeaderChannel.toRaw =
      [(WriteBuffer.effectHeaderChannel.pulled input.1.header).toRaw] := by
    rw [request_interactions _ _ _]
    simp [WriteBuffer.effectHeaderChannel,requestChannel,circuit_norm]
  have proj (i : Var I F) : eval env i.1.header = (eval env i).1.header := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- A physical classifier publishes the complete classified request. -/
theorem request_output_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Request field) 0 env
    (requestComponent (p := SP1Prime)).operations.interactionValuesWith requestChannel.toRaw env =
      [requestChannel.pushedIfValue r.2 r.1] := by
  let I := ProvablePair Request field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main requestCircuit requestGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [requestChannel.pushedIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1]
  rw [Guarded.main_interactionValuesWith]
  change (((requestMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((requestMain input.1).operations (size I)).interactionsWith requestChannel.toRaw =
      [(requestChannel.pushed input.1).toRaw] := by
    rw [request_interactions _ _ _]
    simp [WriteBuffer.effectHeaderChannel,requestChannel,circuit_norm]
  have proj (i : Var I F) : eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushed,Channel.pushedValue,Channel.pushedIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- A physical dispatcher consumes its complete classified request. -/
theorem dispatch_request_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Dispatch field) 0 env
    (dispatchComponent (p := SP1Prime)).operations.interactionValuesWith requestChannel.toRaw env =
      [requestChannel.pulledIfValue r.2 r.1.request] := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main dispatchCircuit dispatchGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [requestChannel.pulledIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1.request]
  rw [Guarded.main_interactionValuesWith]
  change (((dispatchMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((dispatchMain input.1).operations (size I)).interactionsWith requestChannel.toRaw =
      [(requestChannel.pulled input.1.request).toRaw] := by
    rw [dispatch_ledger _ _ _ (by simp [requestChannel,Channels.byteChannel,circuit_norm])]
    simp [requestChannel,cursorChannel,queueEffectChannel,recordChannel,positionChannel,circuit_norm]
  have proj (i : Var I F) : eval env i.1.request = (eval env i).1.request := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- An active classifier selects its released route from the complete bounded descriptor. -/
theorem request_valid_at (env : Environment F) (checked : (requestComponent (p := SP1Prime)).operations.ConstraintsHold env) :
    let r := valueFromOffset (ProvablePair Request field) 0 env
    IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  have assumed : requestComponent.CircuitAssumptions env := fun _ => trivial
  apply (Component.weakSoundness assumed checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (requestComponent.inChannelsOrGuarantees env)]
  intro ch member
  change ch ∈ [WriteBuffer.effectHeaderChannel.toRaw] at member
  obtain rfl := List.mem_singleton.mp member
  exact Operations.channelGuarantees_of_trivial _ (by simp [WriteBuffer.effectHeaderChannel,Channel.toRaw]) _ _

end SP1Clean.WriteEffects
