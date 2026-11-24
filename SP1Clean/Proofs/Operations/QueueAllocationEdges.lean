import SP1Clean.Proofs.Operations.WriteAllocation
import SP1Clean.Proofs.Operations.HintQueueSnapshot
import SP1Clean.Math.SP1Field

/-! # Physical global-queue edges of allocating calls and the target seal -/

namespace SP1Clean
open Circuit Air.Flat Semantics HostHintQueue
private abbrev F := ZMod SP1Prime

namespace WriteAllocation

/-- The complete guarded global state replacement made by one allocating WRITE. -/
def queueValues (r : Open F × F) : List (Interaction F) :=
  [stateChannel.pulledIfValue r.2 r.1.previous, stateChannel.pushedIfValue r.2 r.1.outgoing]

private theorem open_queue_values (r : Var Open F) (env : Environment F) (n : Nat) :
    ((openMain r).operations n).interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (ProvableStruct.eval env r).previous,
       stateChannel.pushedValue (ProvableStruct.eval env r).outgoing] := by
  have occurrences : ((openMain r).operations n).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled r.previous).toRaw,(stateChannel.pushed r.outgoing).toRaw] := by
    rw [open_ledger]
    simp [stateChannel,WriteEffects.queueEffectChannel,cursorChannel,circuit_norm]
  rw [Operations.interactionValuesWith,occurrences]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.eval_pushed]
  rcases r with ⟨⟨_,_,_,_,_⟩,⟨_,_,_,_⟩,⟨_,_,_,_⟩,_,_⟩
  simp only [Open.outgoing,
    ClockParts.high24,ClockParts.low24,circuit_norm]

/-- Both physical queue occurrences, retaining the input row's original activity. -/
theorem openInput_queue (env : Environment F) :
    openComponent.operations.interactionValuesWith stateChannel.toRaw env =
      queueValues (valueFromOffset (ProvablePair Open field) 0 env) := by
  let I := ProvablePair Open field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main openCircuit openSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((openMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [open_queue_values]
  have project (i : Var (ProvablePair Open field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons, List.map_nil, Channel.pulledValue, Channel.pushedValue,Channel.pulledIfValue,
    Channel.pushedIfValue,mul_one,Guarded.eval_activity,project,input,eval_varFromOffset_valueFromOffset,queueValues,I]

/-- An enabled header authenticates its own strict global queue timestamp from local constraints. -/
theorem openInput_valid (env : Environment F) (checked : openComponent.operations.ConstraintsHold env) :
    let r := valueFromOffset (ProvablePair Open field) 0 env
    IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
  let I := ProvablePair Open field
  let input := varFromOffset I (F := F) 0
  let g := Guarded.circuit (openCircuit (p := SP1Prime)) openSupported
  have facts : IsBool (eval env input).2 ∧ ((eval env input).2 = 1 → (eval env input).1.Valid) := by
    apply (g.original_full_soundness (size I) env input (fun _ => trivial) ((Component.constraintsHold_iff _).mp checked) ?_).1
    rw [Operations.guarantees_iff _ _ _ (g.in_channels_or_guarantees_full input _ env)]
    intro ch member
    have known : ch = WriteEffects.queueEffectChannel.toRaw ∨ ch = stateChannel.toRaw ∨ ch = cursorChannel.toRaw := by
      simpa [g,openCircuit,openElaborated,ClockOrder.circuit,ClockOrder.elaborated,circuit_norm,or_comm,or_assoc,or_left_comm] using member
    rcases known with rfl|rfl|rfl <;> exact Operations.channelGuarantees_of_trivial _
      (by simp [WriteEffects.queueEffectChannel,stateChannel,cursorChannel,Channel.toRaw]) _ _
  simpa only [input,eval_varFromOffset_valueFromOffset] using facts

end WriteAllocation

namespace HostHintSnapshot.Seal

private theorem checked_queue (hints : List Bytes) (env : Environment F)
    (checked : (component hints).operations.ConstraintsHold env) :
    (component hints).operations.interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (valueFromOffset Inputs 0 env).2.1,
       stateChannel.pushedValue (HostHintQueueBoundary.initial hints)] := by
  let r : Var Inputs F := varFromOffset Inputs 0
  have cells : eval env r = valueFromOffset Inputs 0 env := eval_varFromOffset_valueFromOffset ..
  have c := (Component.constraintsHold_iff env).mp checked
  change ((main hints r).operations (size Inputs)).ConstraintsHold env at c
  simp only [main,circuit_norm] at c
  have ticket := c _ (Or.inl rfl)
  have count := c _ (Or.inr rfl)
  rw [eval_sub,sub_eq_zero] at ticket count
  have enabled : env r.2.2 = 1 := count.trans ticket
  have occurrences : ((main hints r).operations (size Inputs)).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled r.2.1).toRaw,(stateChannel.pushedIf r.2.2 (const (HostHintQueueBoundary.initial hints))).toRaw] := by
    rw [Operations.interactionsWith,ledger]
    simp [stateChannel,channel,Channel.toRaw,circuit_norm]
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change (((main hints r).operations (size Inputs)).interactionsWith stateChannel.toRaw).map _ = _
  rw [occurrences,← cells]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.eval_pushedIf,ProvableType.eval_const]
  simp only [enabled,Channel.pushedIfValue,Channel.pushedValue,circuit_norm]

/-- The unique checked seal consumes the genuine final global state and reproduces
the public target initial token which the original boundary verifier consumes. -/
theorem physical_queue_ledger (hints : List Bytes) (t : Table F) (same : t.component = component hints)
    (checked : t.Constraints) :
    t.interactionsWith stateChannel.toRaw =
      [stateChannel.pulledValue (physicalState hints t same),stateChannel.pushedValue (HostHintQueueBoundary.initial hints)] := by
  obtain ⟨row,one⟩ := List.length_eq_one_iff.mp (physical_height hints t same)
  have c := checked row (one ▸ List.mem_singleton_self row)
  rw [same] at c
  simpa only [Table.interactionsWith,physicalState,one,List.flatMap_singleton,same,List.getElem_cons_zero] using checked_queue hints _ c

end HostHintSnapshot.Seal
end SP1Clean
