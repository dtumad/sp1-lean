import SP1Clean.Math.SP1Field
import SP1Clean.Proofs.Completeness.WriteAllocationWordTables
import ToClean.Circuit.EmittedInteraction

/-! # Signed block traffic of the grouped placement and allocation-word tables

Both placement pulls and the two independently gated allocation-word sites are present on every
physical row. The direct push uses the checked auxiliary cell for its multiplicity.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical

private abbrev F := ZMod SP1Prime

/-- Two pull sites per grouped placement, including ignored streams and demand padding. -/
def groupBlocks (r : Group F × F) : List (Interaction F) :=
  [blockChannel.pulledIfValue (r.2*r.1.leftGate) (r.1.block false),
   blockChannel.pulledIfValue (r.2*r.1.rightGate) (r.1.block true)]

private theorem group_values (r : Var Group F) (n : Nat) (env : Environment F) :
    ((groupMain r).operations n).interactionValuesWith blockChannel.toRaw env =
      [blockChannel.pulledIfValue (ProvableStruct.eval env r).leftGate ((ProvableStruct.eval env r).block false),
       blockChannel.pulledIfValue (ProvableStruct.eval env r).rightGate ((ProvableStruct.eval env r).block true)] := by
  have raw : ((groupMain r).operations n).interactionsWith blockChannel.toRaw =
      [(blockChannel.pulledIf r.leftGate (r.block false)).toRaw,(blockChannel.pulledIf r.rightGate (r.block true)).toRaw] := by
    rw [Operations.interactionsWith,group_ledger]
    simp [octetsChannel,sliceChannel,positionChannel,blockChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulledIf]
  rcases r with ⟨_,⟨_,_,_,_,_⟩,⟨_,_,_,_,_,_,_,_,_,_⟩,_,_,_,_,_,_,_,_,_⟩
  simp only [Group.leftGate,Group.rightGate,Group.block,circuit_norm]

private theorem groupInput_blocks (env : Environment F) :
    (groupComponent (p := SP1Prime)).operations.interactionValuesWith blockChannel.toRaw env =
      groupBlocks (groupComponent.rowInput env) := by
  let I := ProvablePair Group field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main groupCircuit groupGuardSupported input).operations (size I)).interactionValuesWith _ env =
    groupBlocks (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((groupMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [group_values]
  have proj (i : Var (ProvablePair Group field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.pulledIfValue,Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset,groupBlocks]

/-- The grouped placement table filled at Clean's demand-mode height. -/
def groupTable (rows : List (Group F)) (data : ProverData F) (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table F :=
  Table.ofInputs groupComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- Physical grouped placements satisfy all constraints and guarantees for their generated windows. -/
theorem groupTable_valid (rows : List (Group F)) (honest : ∀ r ∈ rows, r.Valid ∧ r.HonestCoordinates)
    (data : ProverData F) (fit) : (groupTable rows data fit).Constraints ∧ (groupTable rows data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all (fun r : Group F => r.Valid ∧ r.HonestCoordinates) honest

/-- Full signed block ledger, preserving left and right occurrences even at zero activity. -/
theorem groupTable_blocks (rows : List (Group F)) (data : ProverData F) (fit) :
    (groupTable rows data fit).interactionsWith blockChannel.toRaw = (WitnessGeneration.guardedRows rows).flatMap groupBlocks :=
  Table.ofInputs_ledger groupComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial) blockChannel.toRaw groupBlocks groupInput_blocks

end SP1Clean.WriteEffects

namespace SP1Clean.WriteAllocation.Words
open Circuit Air.Flat WriteEffects
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Both the returned-block pull and direct-block supply use the shared word bytes. -/
def blockTraffic (r : Row F × F) : List (Interaction F) :=
  [blockChannel.pulledIfValue (r.2*r.1.hookGate) r.1.returned,
   blockChannel.emittedValue (r.2*(r.1.directGate*r.1.blockReads)) r.1.direct]

private theorem word_block_values (r : Var Row F) (n : Nat) (env : Environment F) :
    ((wordMain r).operations n).interactionValuesWith blockChannel.toRaw env =
      [blockChannel.pulledIfValue (ProvableStruct.eval env r).hookGate (ProvableStruct.eval env r).returned,
       blockChannel.emittedValue (env (var ⟨n⟩)) (ProvableStruct.eval env r).direct] := by
  have raw : ((wordMain r).operations n).interactionsWith blockChannel.toRaw =
      [(blockChannel.pulledIf r.hookGate r.returned).toRaw,(blockChannel.emitted (var ⟨n⟩) r.direct).toRaw] := by
    rw [Operations.interactionsWith,word_ledger]
    simp [cursorChannel,blockChannel,HostHintQueue.wordChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulledIf,Channel.eval_emitted]
  have z : Eval.eval env (0 : fields 3 (Expression F)) = (0 : fields 3 F) := by
    change eval env (#v[0,0,0] : fields 3 (Expression F)) = #v[0,0,0]
    simp only [circuit_norm]
  rcases r with ⟨⟨⟨_,_,_,_,_⟩,_,_⟩,_,_,_,⟨_,_⟩,_,_⟩
  simp only [z,Row.hookGate,Row.returned,Row.direct,Payload.used,circuit_norm]

private theorem wordInput_blocks (env : Environment F) (valid : (wordComponent (p := SP1Prime)).operations.ConstraintsHold env)
    (binary : IsBool (wordComponent.rowInput env).2) :
    wordComponent.operations.interactionValuesWith blockChannel.toRaw env = blockTraffic (wordComponent.rowInput env) := by
  let I := ProvablePair Row field
  let input := varFromOffset I (F := F) 0
  have proj (i : Var (ProvablePair Row field) F) : ProvableStruct.eval env i.1 = (eval env i).1 := by simp only [circuit_norm]
  have flag : env input.2 = (wordComponent.rowInput env).2 := by
    simp only [input,Guarded.eval_activity,eval_varFromOffset_valueFromOffset,Component.rowInput]
    rfl
  have gate (x : Var Row F) : env (x.directGate*x.blockReads) =
      (ProvableStruct.eval env x).directGate*(ProvableStruct.eval env x).blockReads := by
    rcases x with ⟨⟨⟨_,_,_,_,_⟩,_,_⟩,_,_,_,⟨_,_⟩,_,_⟩
    simp only [Row.directGate,circuit_norm]
  have mult : env input.2 * env (var ⟨size I⟩) =
      env input.2 * ((ProvableStruct.eval env input.1).directGate*(ProvableStruct.eval env input.1).blockReads) := by
    rcases binary with off | on
    · simp [flag,off]
    · have raw := (wordComponent.constraintsHold_iff env).mp valid
      have active := Guarded.constraints_of_active wordCircuit wordSupported input (size I) env (flag.trans on) raw
      exact congrArg (env input.2 * ·) ((word_supply input.1 (size I) env active).trans (gate input.1))
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main wordCircuit wordSupported input).operations (size I)).interactionValuesWith _ env =
    blockTraffic (valueFromOffset I 0 env)
  rw [Guarded.main_interactionValuesWith]
  change (((wordMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  rw [word_block_values]
  simp only [Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset] at mult
  simp only [List.map_cons,List.map_nil,Channel.pulledIfValue,Channel.emittedValue,mult,
    Guarded.eval_activity,proj,input,eval_varFromOffset_valueFromOffset,blockTraffic]

/-- Both original block occurrences of every allocation word. The direct push weight is proved
from the generated auxiliary and the guarded constraints, including on inactive rows. -/
theorem wordTable_blocks (rows : List (Row F)) (honest : ∀ r ∈ rows, r.Valid) (data : ProverData F) (fit) :
    (wordTable rows data fit).interactionsWith blockChannel.toRaw = (WitnessGeneration.guardedRows rows).flatMap blockTraffic := by
  let inputs := WitnessGeneration.guardedRows (F := F) rows
  let c := wordComponent (p := SP1Prime)
  let actual := c.inputData inputs data
  have all := WitnessGeneration.guardedRows_all (F := F) Row.Valid honest
  unfold wordTable Table.ofInputs
  refine (Table.build_interactions c inputs actual (.empty _) _ _ _ blockChannel.toRaw).trans ?_
  apply List.flatMap_congr
  intro r member
  let env := Environment.fromArray (c.buildRow r actual (.empty _)) actual
  have checked := (c.buildRow_constraintsHold r actual (.empty _) (all r member)).1
  have value := c.rowInput_buildRow r actual actual (.empty _)
  change c.rowInput env = r at value
  have one := wordInput_blocks env checked (value ▸ (all r member).1)
  exact one.trans (congrArg blockTraffic value)

end SP1Clean.WriteAllocation.Words
