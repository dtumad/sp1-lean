import SP1Clean.Math.SP1Field
import SP1Clean.Proofs.Operations.WriteAllocation
import SP1Clean.Proofs.Operations.WriteAllocationWords
import SP1Clean.Proofs.Operations.HintQueueSnapshot
import ToClean.Circuit.EmittedInteraction

/-! # Physical immutable-record consumers and dynamic publications

The snapshot metadata and word gates are Boolean. Each fresh node and each fresh word
publishes its typed payload at the original activity times the stored reader count.
-/

namespace SP1Clean.HintRecordPublications
open Circuit Air.Flat Semantics HintQueue HostHintQueue
private abbrev F := ZMod SP1Prime
open WriteAllocation

/-- Signed immutable metadata publication of a physical allocation step, including zero counts. -/
theorem node_row (env : Environment F) :
    let r := valueFromOffset (ProvablePair Step field) 0 env
    stepComponent.operations.interactionValuesWith nodeChannel.toRaw env =
      [nodeChannel.emittedValue (r.2 * r.1.readers) r.1.node.node] := by
  let I := ProvablePair Step field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main stepCircuit stepSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((stepMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((stepMain input.1).operations (size I)).interactionsWith nodeChannel.toRaw =
      [(nodeChannel.emitted input.1.readers input.1.node.node).toRaw] := by
    rw [step_ledger _ _ _ (by simp [nodeChannel, Channels.byteChannel, circuit_norm])]
    simp [cursorChannel, WriteEffects.recordChannel, nodeChannel, contentsChannel, circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  have cells : eval env input = valueFromOffset I 0 env := eval_varFromOffset_valueFromOffset ..
  rw [← cells]
  have msg (r : Var I F) : eval env r.1.node.node = (eval env r).1.node.node := by simp only [I,circuit_norm]
  have count (r : Var I F) : env r.1.readers = (eval env r).1.readers := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.eval_emitted,Channel.emittedValue,Guarded.eval_activity,msg,count]

/-- Signed immutable word publication, including the disabled padding rows. -/
theorem word_row (env : Environment F) :
    let r := valueFromOffset (ProvablePair Words.Row field) 0 env
    Words.wordComponent.operations.interactionValuesWith wordChannel.toRaw env =
      [wordChannel.emittedValue (r.2 * r.1.wordReads) r.1.word] := by
  let I := ProvablePair Words.Row field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main Words.wordCircuit Words.wordSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((Words.wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((Words.wordMain input.1).operations (size I)).interactionsWith wordChannel.toRaw =
      [(wordChannel.emitted input.1.wordReads input.1.word).toRaw] := by
    rw [Operations.interactionsWith, Words.word_ledger]
    simp [Words.cursorChannel, WriteEffects.blockChannel, wordChannel, circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  have cells : eval env input = valueFromOffset I 0 env := eval_varFromOffset_valueFromOffset ..
  rw [← cells]
  have msg (r : Var I F) : eval env r.1.word = (eval env r).1.word := by
    rcases r with ⟨⟨⟨_,_,_⟩,_,_,_,⟨_,_⟩,_,_⟩,_⟩
    simp [I,Words.Row.word,Words.Payload.last,Words.Payload.more,Word.ofBytes,circuit_norm]
  have count (r : Var I F) : env r.1.wordReads = (eval env r).1.wordReads := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.eval_emitted,Channel.emittedValue,Guarded.eval_activity,msg,count]

private theorem boolean_check (env : Environment F) (x : Expression F) (h : env (x * (x - 1)) = 0) : IsBool (env x) := by
  apply IsBool.iff_mul_sub_one.mpr
  simpa only [eval_mul,eval_sub,Expression.eval] using h

/-- Raw snapshot constraints force every immutable-record interaction to be a unit pull or inactive. -/
theorem snapshot_pulls (hints : List Bytes) (ch : RawChannel F)
    (which : ch = nodeChannel.toRaw ∨ ch = wordChannel.toRaw) (env : Environment F)
    (checked : (HostHintSnapshot.component hints).operations.ConstraintsHold env) :
    ∀ i ∈ (HostHintSnapshot.component hints).operations.interactionValuesWith ch env, ¬i.Push := by
  let input := varFromOffset HostHintSnapshot.Inputs (F := F) 0
  have checks := (Component.constraintsHold_iff env).mp checked
  change ((HostHintSnapshot.main hints input).operations (size HostHintSnapshot.Inputs)).ConstraintsHold env at checks
  simp only [HostHintSnapshot.main,circuit_norm] at checks
  have first := boolean_check env input.1.first (checks _ (Or.inr (Or.inr (Or.inl rfl))))
  have live := boolean_check env input.1.active (checks _ (Or.inr (Or.inr (Or.inr rfl))))
  intro i mem
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at mem
  change i ∈ (((HostHintSnapshot.main hints input).operations (size HostHintSnapshot.Inputs)).interactionsWith ch).map _ at mem
  rcases which with rfl | rfl
  · have raw : ((HostHintSnapshot.main hints input).operations (size HostHintSnapshot.Inputs)).interactionsWith nodeChannel.toRaw =
        [(nodeChannel.pulledIf input.1.first (input.1.node input.2.1)).toRaw] := by
      rw [Operations.interactionsWith, HostHintSnapshot.ledger]
      simp [HostHintSnapshot.channel,nodeChannel,wordChannel,Channel.toRaw,circuit_norm]
    rw [raw] at mem
    obtain rfl := List.mem_singleton.mp mem
    apply Interaction.not_push_iff.mpr
    exact first.imp_right (fun h => ⟨rfl,h⟩)
  · have raw : ((HostHintSnapshot.main hints input).operations (size HostHintSnapshot.Inputs)).interactionsWith wordChannel.toRaw =
        [(wordChannel.pulledIf input.1.active (input.1.word input.2.1)).toRaw] := by
      rw [Operations.interactionsWith, HostHintSnapshot.ledger]
      simp [HostHintSnapshot.channel,nodeChannel,wordChannel,Channel.toRaw,circuit_norm]
    rw [raw] at mem
    obtain rfl := List.mem_singleton.mp mem
    apply Interaction.not_push_iff.mpr
    exact live.imp_right (fun h => ⟨rfl,h⟩)
end SP1Clean.HintRecordPublications
