import SP1Clean.Proofs.Operations.WriteDispatch
import SP1Clean.Proofs.Operations.HintRecordPublications

/-! # Physical metadata requests of WRITE dispatchers and newly allocated nodes -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Physical dispatch rows have Boolean activity and, when enabled, the checked chronological
dispatch contract. The only nontrivial channel guarantee is the genuine SP1 Byte guarantee. -/
theorem dispatch_valid_at (env : Environment F) (checked : (dispatchComponent (p := SP1Prime)).operations.ConstraintsHold env)
    (bytes : dispatchComponent.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    let r := valueFromOffset (ProvablePair Dispatch field) 0 env
    IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  let g := Guarded.circuit (dispatchCircuit (p := SP1Prime)) dispatchGuardSupported
  have facts : IsBool (eval env input).2 ∧ ((eval env input).2 = 1 → (eval env input).1.Valid) := by
    apply (g.original_full_soundness (size I) env input (fun _ => trivial) ((Component.constraintsHold_iff _).mp checked) ?_).1
    rw [Operations.guarantees_iff _ _ _ (g.in_channels_or_guarantees_full input _ env)]
    intro ch member
    have known : ch = requestChannel.toRaw ∨ ch = cursorChannel.toRaw ∨ ch = Channels.byteChannel.toRaw ∨
        ch = recordChannel.toRaw ∨ ch = positionChannel.toRaw := by
      simpa [g,dispatchCircuit,dispatchElaborated,flagsCircuit,flagsElaborated,AddressSum.circuit,AddressSum.elaborated,
        WriteStart.circuit,WriteStart.elaborated,circuit_norm,or_assoc,or_comm,or_left_comm] using member
    rcases known with rfl | rfl | rfl | rfl | rfl
    · exact Operations.channelGuarantees_of_trivial _ (by simp [requestChannel,Channel.toRaw]) _ _
    · exact Operations.channelGuarantees_of_trivial _ (by simp [cursorChannel,Channel.toRaw]) _ _
    · exact (Component.channelGuarantees_iff _ _).mp bytes
    · exact Operations.channelGuarantees_of_trivial _ (by simp [recordChannel,Channel.toRaw]) _ _
    · exact Operations.channelGuarantees_of_trivial _ (by simp [positionChannel,Channel.toRaw]) _ _
  simpa only [input,eval_varFromOffset_valueFromOffset,I] using facts

/-- The classification flags exclusively authorize either a direct buffer, returned hooks,
or an output without an allocation. -/
theorem Dispatch.Valid.allocation_gates {r : Dispatch F} (v : r.Valid) :
    IsBool r.flags.hook ∧ IsBool (r.flags.direct+r.flags.hook) := by
  rw [v.1]
  have routes := flagsFor_choices r.request.route
  simp only [List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at routes
  rcases routes with h | h | h | h | h | h <;> simp [h.1,DispatchFlags.hook,IsBool]

/-- Hook calls read their descriptor, request length and exact number of returned hints. -/
def Dispatch.metadataReads (r : Dispatch F) : List (Record F) :=
  [r.metadata 2 #v[r.request.route,0,0],r.metadata 0 r.length,r.metadata 3 r.returned]

private theorem dispatch_metadata_values (r : Var Dispatch F) (n : Nat) (env : Environment F) :
    ((dispatchMain r).operations n).interactionValuesWith recordChannel.toRaw env =
      (ProvableStruct.eval env r).metadataReads.map (recordChannel.pulledIfValue (ProvableStruct.eval env r).flags.hook) := by
  have raw : ((dispatchMain r).operations n).interactionsWith recordChannel.toRaw =
      [(recordChannel.pulledIf r.flags.hook (r.metadata 2 #v[r.request.route,0,0])).toRaw,
       (recordChannel.pulledIf r.flags.hook (r.metadata 0 r.length)).toRaw,
       (recordChannel.pulledIf r.flags.hook (r.metadata 3 r.returned)).toRaw] := by
    rw [dispatch_ledger _ _ _ (by simp [recordChannel,Channels.byteChannel,circuit_norm])]
    simp [requestChannel,cursorChannel,recordChannel,queueEffectChannel,positionChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [Dispatch.metadataReads,List.map_cons,List.map_nil,Channel.eval_pulledIf]
  rcases r with ⟨⟨⟨_,_,_,_⟩,_⟩,⟨_,_,_,_,_⟩,⟨_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_,_,_,_⟩
  simp only [Dispatch.metadata,Dispatch.length,DispatchFlags.hook,circuit_norm]

/-- All three gated metadata interactions of an arbitrary physical dispatcher row. -/
theorem dispatch_metadata_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Dispatch field) (F := F) 0 env
    dispatchComponent.operations.interactionValuesWith recordChannel.toRaw env =
      r.1.metadataReads.map (recordChannel.pulledIfValue (r.2*r.1.flags.hook)) := by
  let I := ProvablePair Dispatch field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main dispatchCircuit dispatchGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((dispatchMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [dispatch_metadata_values,List.map_map]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [Channel.pulledIfValue,Function.comp_def,Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset,I]
  rfl

end SP1Clean.WriteEffects

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat WriteEffects
open scoped Classical
private abbrev F := ZMod SP1Prime

private theorem step_metadata_values (r : Var Step F) (n : Nat) (env : Environment F) :
    ((stepMain r).operations n).interactionValuesWith recordChannel.toRaw env =
      [recordChannel.pulledIfValue (1-(ProvableStruct.eval env r).direct) (ProvableStruct.eval env r).metadata] := by
  have raw : ((stepMain r).operations n).interactionsWith recordChannel.toRaw =
      [(recordChannel.pulledIf (1-r.direct) r.metadata).toRaw] := by
    rw [step_ledger _ _ _ (by simp [recordChannel,Channels.byteChannel,circuit_norm])]
    simp [cursorChannel,recordChannel,HostHintQueue.nodeChannel,contentsChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulledIf]
  rcases r with ⟨⟨_,⟨_,_,_⟩⟩,_,_,_,_,_⟩
  simp only [Step.metadata,Step.length,circuit_norm]

/-- A returned node requests precisely its own endpoint metadata, including a zero byte length. -/
theorem step_metadata_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Step field) (F := F) 0 env
    stepComponent.operations.interactionValuesWith recordChannel.toRaw env =
      [recordChannel.pulledIfValue (r.2*(1-r.1.direct)) r.1.metadata] := by
  let I := ProvablePair Step field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main stepCircuit stepSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((stepMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [step_metadata_values]
  have proj (i : Var I F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pulledIfValue,Guarded.eval_activity,proj,input,
    eval_varFromOffset_valueFromOffset,I]

end SP1Clean.WriteAllocation
