import SP1Clean.Proofs.Operations.WritePlacementPlans
import SP1Clean.Proofs.Operations.WriteOctetRows
import SP1Clean.Proofs.Completeness.WriteBlockLedgers
import SP1Clean.Proofs.Completeness.WriteBufferTables
import SP1Clean.Proofs.Completeness.WriteDispatchTable

/-! # Constructing the native WRITE effect tables

Every span supplies its entire header for classification, and every aligned word supplies its original address, clock and value.
The dispatcher takes each classified request at that same clock. The ledgers retain every physical padding occurrence.
-/

namespace SP1Clean.WriteEffects
open Air.Flat Circuit
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- One guarded classifier row for every full WRITE header. -/
def requestTable (rows : List (Request F)) (data : ProverData F) (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table F :=
  Table.ofInputs requestComponent (WitnessGeneration.guardedRows rows) data ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- Decode every physical aligned word before trimming or dispatching its bytes. -/
def octetTable (rows : List (WordRow F)) (data : ProverData F) (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table F :=
  Table.ofInputs wordComponent (WitnessGeneration.guardedRows rows) data ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

/-- Classifiers pull exactly their full incoming headers. -/
theorem requestTable_headers (rows : List (Request F)) (data : ProverData F) (fit) :
    (requestTable rows data fit).interactionsWith WriteBuffer.effectHeaderChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => WriteBuffer.effectHeaderChannel.pulledIfValue r.2 r.1.header) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger requestComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
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

/-- Each classified request is emitted once at its physical activity. -/
theorem requestTable_requests (rows : List (Request F)) (data : ProverData F) (fit) :
    (requestTable rows data fit).interactionsWith requestChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => requestChannel.pushedIfValue r.2 r.1) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger requestComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
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

/-- Decoders pull the exact incoming clock, aligned address and data word. -/
theorem octetTable_words (rows : List (WordRow F)) (data : ProverData F) (fit) :
    (octetTable rows data fit).interactionsWith WriteBuffer.wordChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => WriteBuffer.wordChannel.pulledIfValue r.2 r.1.read) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger wordComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  exact decoder_word_at

/-- The chronological dispatcher receives the complete request, including its classified route. -/
theorem dispatchTable_requests (rows : List (Dispatch F)) (data : ProverData F) (fit) :
    (dispatchTable rows data fit).interactionsWith requestChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => requestChannel.pulledIfValue r.2 r.1.request) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger dispatchComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  intro env
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

/-- Each decoder publishes eight checked byte lanes at its original guest key and clock. -/
theorem octetTable_octets (rows : List (WordRow F)) (data : ProverData F) (fit) :
    (octetTable rows data fit).interactionsWith octetsChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => octetsChannel.pushedIfValue r.2 (r.1.octets (256 : F)⁻¹)) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger wordComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  exact decoder_octets_at

/-- Even an ignored placement consumes its original full octet occurrence. -/
theorem groupTable_octets (rows : List (Group F)) (data : ProverData F) (fit) :
    (groupTable rows data fit).interactionsWith octetsChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => octetsChannel.pulledIfValue r.2 r.1.octets) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger groupComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  exact group_octets_at

/-- Every guest group consumes its own alignment plan, including ignored or empty windows. -/
theorem groupTable_plans (rows : List (Group F)) (data : ProverData F) (fit) :
    (groupTable rows data fit).interactionsWith sliceChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => sliceChannel.pulledIfValue r.2 r.1.plan) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger groupComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  exact group_plan_at

end SP1Clean.WriteEffects
