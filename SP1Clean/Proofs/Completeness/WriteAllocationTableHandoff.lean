import SP1Clean.Proofs.Completeness.WriteAllocationCursorBalance

/-! # Fresh node and word authorizations on the same ordered allocation rows

One node produces each contents record and one seed consumes it. The original node and seed tables each retain a physical
occurrence for every demand-padding row, and balance holds for each repeated query.
-/

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat Semantics HintQueue WriteEffects
open scoped Classical

private abbrev F := ZMod SP1Prime

private theorem step_values (r : Var Step F) (n : Nat) (env : Environment F) :
    ((stepMain r).operations n).interactionValuesWith contentsChannel.toRaw env =
      [contentsChannel.pushedValue (ProvableStruct.eval env r).contents] := by
  have raw : ((stepMain r).operations n).interactionsWith contentsChannel.toRaw =
      [(contentsChannel.pushed r.contents).toRaw] := by
    rw [step_ledger _ _ _ (by simp [contentsChannel, Channels.byteChannel, circuit_norm])]
    simp [cursorChannel, recordChannel, HostHintQueue.nodeChannel, contentsChannel, circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pushed,List.cons.injEq,and_true]
  rcases r with ⟨⟨_,⟨_,_,_⟩⟩,_,_,_,_,_⟩
  simp only [Step.contents,Step.length,scale,circuit_norm]

/-- Every fresh node emits its contents authorization at the original activity. -/
theorem stepTable_contents (rows : List (Step F)) (data : ProverData F) (fit) :
    (stepTable rows data fit).interactionsWith contentsChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => contentsChannel.pushedIfValue r.2 r.1.contents) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger stepComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
  let I := ProvablePair Step field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main stepCircuit stepSupported input).operations (size I)).interactionValuesWith _ env =
    [contentsChannel.pushedIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1.contents]
  rw [Guarded.main_interactionValuesWith]
  change (((stepMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [step_values]
  have proj (i : Var (ProvablePair Step field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by
    simp only [circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pushedValue,Channel.pushedIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- Each allocated word seed consumes the full authorization once, at its physical guard. -/
theorem Words.seedTable_contents (rows : List (Contents F)) (data : ProverData F) (fit) :
    (Words.seedTable rows data fit).interactionsWith contentsChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => contentsChannel.pulledIfValue r.2 r.1) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger Words.seedComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
  let I := ProvablePair Contents field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main Words.seedCircuit Words.seedSupported input).operations (size I)).interactionValuesWith _ env =
    [contentsChannel.pulledIfValue (valueFromOffset I 0 env).2 (valueFromOffset I 0 env).1]
  rw [Guarded.main_interactionValuesWith]
  change (((Words.seedMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((Words.seedMain input.1).operations (size I)).interactionsWith contentsChannel.toRaw =
      [(contentsChannel.pulled input.1).toRaw] := by
    rw [Operations.interactionsWith,Words.seed_ledger]
    simp [contentsChannel,Words.cursorChannel,circuit_norm]
  have proj (i : Var (ProvablePair Contents field) F) : eval env i.1 = (eval env i).1 := by simp only [circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset]

/-- Matching node and seed tables cancel at each serialized authorization, including repeated
messages and disabled occurrences. -/
theorem contents_balanced (rows : List (Step F)) (data : ProverData F) (hn hs) :
    LogUpBalanced ((stepTable rows data hn).interactionsWith contentsChannel.toRaw ++
      (Words.seedTable (rows.map Step.contents) data hs).interactionsWith contentsChannel.toRaw) := by
  intro msg
  rw [balanceOf_append,stepTable_contents,Words.seedTable_contents,
    WitnessGeneration.guarded_push_sum contentsChannel _ Step.contents]
  have pulls := WitnessGeneration.guarded_pull_sum contentsChannel (rows.map Step.contents) (fun x => x) msg
  rw [pulls,List.map_id' _]
  rw [← balanceOf_append]
  exact contentsChannel.logUp_unit_of_perm (List.Perm.refl _) msg

end SP1Clean.WriteAllocation
