import SP1Clean.Proofs.Completeness.WriteAllocationCursorTables
import SP1Clean.Proofs.Completeness.WriteBlockLedgers
import ToClean.Air.GuardedLedger

/-! # Counted immutable-node and word emissions on their original allocation tables

Both expressions use the original row-authorized multiplicity and its activity gate. Clean demand padding remains
present in physical order, even when the node or word has zero readers.
-/

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat WriteEffects
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Each occupied or padded allocation node emits its immutable metadata at its carried reader count. -/
theorem stepTable_nodes (rows : List (Step F)) (data : ProverData F) (fit) :
    (stepTable rows data fit).interactionsWith HostHintQueue.nodeChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun x => HostHintQueue.nodeChannel.emittedValue (x.2*x.1.readers) x.1.node.node) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger stepComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
  let I := ProvablePair Step field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main stepCircuit stepSupported input).operations (size I)).interactionValuesWith _ env =
    [HostHintQueue.nodeChannel.emittedValue ((valueFromOffset I 0 env).2 * (valueFromOffset I 0 env).1.readers) (valueFromOffset I 0 env).1.node.node]
  rw [Guarded.main_interactionValuesWith]
  change (((stepMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have site : ((stepMain input.1).operations (size I)).interactionsWith HostHintQueue.nodeChannel.toRaw =
      [(HostHintQueue.nodeChannel.emitted input.1.readers input.1.node.node).toRaw] := by
    rw [step_ledger _ _ _ (by simp [HostHintQueue.nodeChannel,Channels.byteChannel,circuit_norm])]
    simp [cursorChannel,recordChannel,contentsChannel,HostHintQueue.nodeChannel,circuit_norm]
  have payload (i : Var I F) : eval env i.1.node.node = (eval env i).1.node.node := by
    simp only [I,circuit_norm]
  have readers (i : Var I F) : env i.1.readers = (eval env i).1.readers := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,site]
  simp only [List.map_cons,List.map_nil,Channel.eval_emitted,Channel.emittedValue,
    Guarded.eval_activity,payload,readers,input,eval_varFromOffset_valueFromOffset]

/-- Every allocation word retains its immutable queue reader count and all bytes independently of block-channel funding. -/
theorem wordTable_queueWords (rows : List (Words.Row F)) (data : ProverData F) (fit) :
    (Words.wordTable rows data fit).interactionsWith HostHintQueue.wordChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun x => HostHintQueue.wordChannel.emittedValue (x.2*x.1.wordReads) x.1.word) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger Words.wordComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
  let I := ProvablePair Words.Row field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main Words.wordCircuit Words.wordSupported input).operations (size I)).interactionValuesWith _ env =
    [HostHintQueue.wordChannel.emittedValue ((valueFromOffset I 0 env).2 * (valueFromOffset I 0 env).1.wordReads) (valueFromOffset I 0 env).1.word]
  rw [Guarded.main_interactionValuesWith]
  change (((Words.wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have site : ((Words.wordMain input.1).operations (size I)).interactionsWith HostHintQueue.wordChannel.toRaw =
      [(HostHintQueue.wordChannel.emitted input.1.wordReads input.1.word).toRaw] := by
    rw [Operations.interactionsWith,Words.word_ledger]
    simp [Words.cursorChannel,WriteEffects.blockChannel,HostHintQueue.wordChannel,circuit_norm]
  have payload (i : Var I F) : eval env i.1.word = (eval env i).1.word := by
    rcases i with ⟨⟨⟨⟨_,_,_,_,_⟩,_,_⟩,_,_,_,⟨_,_⟩,_,_⟩,_⟩
    simp only [I,Words.Row.word,Words.Payload.last,Words.Payload.more,Word.ofBytes,circuit_norm]
  have readers (i : Var I F) : env i.1.wordReads = (eval env i).1.wordReads := by simp only [I,circuit_norm]
  rw [Operations.interactionValuesWith,site]
  simp only [List.map_cons,List.map_nil,Channel.eval_emitted,Channel.emittedValue,
    Guarded.eval_activity,payload,readers,input,eval_varFromOffset_valueFromOffset]

end SP1Clean.WriteAllocation
