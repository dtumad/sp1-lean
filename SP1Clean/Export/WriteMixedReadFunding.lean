import SP1Clean.Export.WriteGeneratedSelection
import SP1Clean.Export.WriteMixedSourceRecords

/-! # Funding every WRITE read from its genuine mixed physical source

The released execution determines the ordinary, ECALL, HINT_READ, refresh and finalizer rows.
Each repeated x12 or buffer request selects a covering predecessor in that same assembled
supervisor. A request can therefore be routed without additional clock, coverage or row evidence.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Semantics Soundness TraceGen Machine FormalModel.Shard
open WriteProbe WriteBuffer WriteProbe.AccessInventory WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F)
    (header : SP1PublicIO F) (remaining : Remaining image source target finish)

/-- A classified ordinary, ECALL, HINT_READ or refresh transfer is positively funded at its original generated site. -/
theorem predecessor_mem_live {id : Source} {r : Readback F} (chosen : GeneratedPredecessor image source events rows id r)
    (packets : List WriteObservations.Packet) : r ∈ Counted.live (records (compiledSource run routed data hint packets)) := by
  let fit := heights run routed
  let generated := compiledSource run routed data hint packets
  have atRow (id : Source) (after : 6 ≤ position id)
      (unit : ∀ eval, ∃ cells ∈ (table rows _ fit data hint id after).table, (1,r) ∈ rowRecords id (Environment.fromArray cells eval)) :
      r ∈ Counted.live (records generated) := by
    obtain ⟨cells, inTable, receipt⟩ := unit (generated id).data
    have physical : cells ∈ (generated id).table := by
      change cells ∈ (compiledSource run routed data hint packets id).table
      rwa [compiledSource_later run routed data hint packets id after]
    have paid : (1,r) ∈ records generated :=
      List.mem_flatMap.mpr ⟨id, sources_complete id, List.mem_flatMap.mpr ⟨cells, physical, receipt⟩⟩
    exact List.mem_map.mpr ⟨(1,r), List.mem_filter.mpr ⟨paid, by simp⟩, rfl⟩
  cases chosen with
  | @ordinary located view f base result touch projected made phase used legal bucket valid =>
    apply atRow (.ordinary result.routed.id) (by change 6 ≤ 7 + _; omega)
    intro eval
    exact generated_ordinary projected made phase used legal _ bucket valid data eval hint (fit.ordinary _)
  | ecall used phase operand =>
    apply atRow (.host .ecall) (by decide)
    intro eval
    exact generated_ecall rows _ _ used phase operand data eval hint fit.ecall
  | @hint entry used =>
    apply atRow (.host (.word entry.1)) (by cases entry.1 <;> decide)
    intro eval
    exact generated_hint run.1 used data eval (fit.hint _)
  | refresh used =>
    apply atRow .refresh (by decide)
    intro eval
    exact generated_refresh _ _ used data eval fit.memory fit.state

variable {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)

include collected

/-- The original generated publishers fund the exact word and incoming WRITE clock of every x12 or buffer read. -/
theorem compiled_funded {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets)) :
    ∃ r ∈ Counted.live (records (compiledSource run routed data hint packets)), Counted.Covers r read := by
  obtain terminal | later := WriteBoundaryBuild.read_source_of_rows run.1 collected routed member data hint
    (compiledSource run routed data hint packets) (fun _ => rfl)
  · exact terminal
  · obtain ⟨id, r, generated, covers⟩ := classify_predecessor run routed later
    exact ⟨r, predecessor_mem_live run routed data hint generated packets, covers⟩

/-- Counted routing succeeds on the generated publishers before installing any other supervisor slot.
Each repeated request remains at its original position in the returned array. -/
theorem compiled_route_exists :
    let reads := (readDemand (packetRows (p := SP1Prime) events packets)).map Prod.snd
    ∃ requests, Counted.route? (Counted.live (records (compiledSource run routed data hint packets))) reads = some requests := by
  apply Counted.route?_exists
  intro read member
  obtain ⟨⟨cut, read⟩, occurs, rfl⟩ := List.mem_map.mp member
  exact compiled_funded run routed data hint collected occurs

/-- Every actual x12 length or aligned buffer read retains its funded source after canonical installation. -/
theorem read_funded {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets)) :
    ∃ r ∈ Counted.live (records (raw (ofExecution run routed finish data hint header remaining packets))), Counted.Covers r read := by
  rw [compiled_records run routed data hint packets finish header remaining]
  exact compiled_funded run routed data hint collected member

/-- The same successful source route is available from the original installed supervisor. -/
theorem route_exists :
    let w := ofExecution run routed finish data hint header remaining packets
    let reads := (readDemand (packetRows (p := SP1Prime) events packets)).map Prod.snd
    ∃ requests, Counted.route? (Counted.live (records (raw w))) reads = some requests := by
  dsimp only
  rw [compiled_records run routed data hint packets finish header remaining]
  exact compiled_route_exists run routed data hint collected

end SP1Clean.Export.WriteMixedSourceTables
