import SP1Clean.Proofs.Operations.WriteGroup
import SP1Clean.Proofs.Operations.WriteEffects
import SP1Clean.Math.SP1Field

/-! # Physical guarded interfaces between sampled RAM words and placement octets -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- A guarded decoder consumes its actual full probe word. -/
theorem decoder_word_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair WordRow field) 0 env
    (wordComponent (p := SP1Prime)).operations.interactionValuesWith WriteBuffer.wordChannel.toRaw env =
      [WriteBuffer.wordChannel.pulledIfValue r.2 r.1.read] := by
  let I := ProvablePair WordRow field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main wordCircuit wordGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [WriteBuffer.wordChannel.pulledIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1.read]
  rw [Guarded.main_interactionValuesWith]
  change (((wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((wordMain input.1).operations (size I)).interactionsWith WriteBuffer.wordChannel.toRaw =
      [(WriteBuffer.wordChannel.pulled input.1.read).toRaw] := by
    rw [word_interactions _ _ _ (by simp [WriteBuffer.wordChannel,Channels.byteChannel,circuit_norm])]
    simp [WriteBuffer.wordChannel,octetsChannel,circuit_norm]
  have proj (i : Var I F) : eval env i.1.read = (eval env i).1.read := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- A guarded decoder publishes all eight lanes at the original key and clock. -/
theorem decoder_octets_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair WordRow field) 0 env
    (wordComponent (p := SP1Prime)).operations.interactionValuesWith octetsChannel.toRaw env =
      [octetsChannel.pushedIfValue r.2 (r.1.octets (256 : F)⁻¹)] := by
  let I := ProvablePair WordRow field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main wordCircuit wordGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [octetsChannel.pushedIfValue (valueFromOffset I 0 env).2 ((valueFromOffset I 0 env).1.octets (256 : F)⁻¹)]
  rw [Guarded.main_interactionValuesWith]
  change (((wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((wordMain input.1).operations (size I)).interactionsWith octetsChannel.toRaw =
      [(octetsChannel.pushed (input.1.octets (.const (256 : F)⁻¹))).toRaw] := by
    rw [word_interactions _ _ _ (by simp [octetsChannel,Channels.byteChannel,circuit_norm])]
    simp [WriteBuffer.wordChannel,octetsChannel,circuit_norm]
  have proj (i : Var I F) : eval env (i.1.octets (.const (256 : F)⁻¹)) = (eval env i).1.octets (256 : F)⁻¹ := by
    rcases i with ⟨⟨⟨_,_,_⟩,_⟩,_⟩
    simp only [I,WordRow.octets,U16toU8OperationSafe.bytes,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushed,Channel.pushedValue,Channel.pushedIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- A physical placement consumes the complete word including unused lanes. -/
theorem group_octets_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Group field) 0 env
    (groupComponent (p := SP1Prime)).operations.interactionValuesWith octetsChannel.toRaw env =
      [octetsChannel.pulledIfValue r.2 r.1.octets] := by
  let I := ProvablePair Group field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main groupCircuit groupGuardSupported input).operations (size I)).interactionValuesWith _ env =
    [octetsChannel.pulledIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1.octets]
  rw [Guarded.main_interactionValuesWith]
  change (((groupMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((groupMain input.1).operations (size I)).interactionsWith octetsChannel.toRaw =
      [(octetsChannel.pulled input.1.octets).toRaw] := by
    rw [Operations.interactionsWith,group_ledger]
    simp [octetsChannel,sliceChannel,positionChannel,blockChannel,circuit_norm]
  have proj (i : Var I F) : eval env i.1.octets = (eval env i).1.octets := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- Every enabled physical decoder extracts the eight bytes of its full read word. -/
theorem decoder_valid_at (env : Environment F) (checked : (wordComponent (p := SP1Prime)).operations.ConstraintsHold env)
    (bytes : wordComponent.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    let r := valueFromOffset (ProvablePair WordRow field) 0 env
    IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  let I := ProvablePair WordRow field
  let input := varFromOffset I (F := F) 0
  let g := Guarded.circuit (wordCircuit (p := SP1Prime)) wordGuardSupported
  have valid : IsBool (eval env input).2 ∧ ((eval env input).2 = 1 → (eval env input).1.Valid) := by
    apply (g.original_full_soundness (size I) env input (fun _ => trivial) ((Component.constraintsHold_iff _).mp checked) ?_).1
    rw [Operations.guarantees_iff _ _ _ (g.in_channels_or_guarantees_full input _ env)]
    intro ch member
    have known : ch = WriteBuffer.wordChannel.toRaw ∨ ch = Channels.byteChannel.toRaw := by
      simpa [g,wordCircuit,wordElaborated,U16toU8OperationSafe.circuit,circuit_norm,or_comm] using member
    rcases known with rfl | rfl
    · exact Operations.channelGuarantees_of_trivial _ (by simp [WriteBuffer.wordChannel,Channel.toRaw]) _ _
    · exact (Component.channelGuarantees_iff _ _).mp bytes
  simpa only [input,eval_varFromOffset_valueFromOffset,I] using valid

end SP1Clean.WriteEffects
