import SP1Clean.Proofs.Operations.WritePlacementPlans
import SP1Clean.Proofs.Operations.WriteRequestRows
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
  exact request_header_at

/-- Each classified request is emitted once at its physical activity. -/
theorem requestTable_requests (rows : List (Request F)) (data : ProverData F) (fit) :
    (requestTable rows data fit).interactionsWith requestChannel.toRaw =
      (WitnessGeneration.guardedRows rows).map (fun r => requestChannel.pushedIfValue r.2 r.1) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger requestComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)
  exact request_output_at

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
  exact dispatch_request_at

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
