import SP1Clean.Export.WriteGeneratedSelection
import SP1Clean.Export.WriteMixedSourceAssembly

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

/-- Construct the 31 registered Memory sources of one released execution with both incoming
boundaries and the exact set of addresses requested by its collected WRITE packets. -/
noncomputable def ofExecution (packets : List WriteObservations.Packet) : EnsembleWitness (base image source target finish) :=
  build image source target finish rows (HintReadTransfers.history image source events) (heights run routed) data hint remaining
    (MixedMemoryHistory.stream image source events rows) (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.canonical run.1 routed) header

/-- All generated Memory sources and incoming boundaries satisfy the canonical global constraints.
Other generators certify only the remaining non-Memory slots. -/
theorem ofExecution_constraints (packets : List WriteObservations.Packet)
    (checked : ∀ i absent, let t := (remaining i absent).1; t.Constraints ∧ t.Guarantees) :
    (ofExecution run routed finish data hint header remaining packets).Constraints :=
  WriteBoundaryBuild.build_constraints image source target finish _ _ (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint header _
    (suffix_registered image source target finish rows _ (heights run routed) data hint remaining)
    (fun t present => (suffix_valid image source target finish rows data hint remaining run routed checked t present).1)

/-- A classified mixed transfer occurs at its original position after canonical assembly. -/
theorem predecessor_mem_live {id : Source} {r : Readback F} (chosen : GeneratedPredecessor image source events rows id r)
    (packets : List WriteObservations.Packet) :
    r ∈ Counted.live (records (raw (ofExecution run routed finish data hint header remaining packets))) := by
  let fit := heights run routed
  cases chosen with
  | @ordinary located view f base result touch projected made phase used legal bucket valid =>
    apply mem_live image source target finish rows _ fit data hint remaining _ _ _ header (.ordinary result.routed.id) (by change 6 ≤ 7 + _; omega)
    intro eval
    exact generated_ordinary projected made phase used legal _ bucket valid data eval hint (fit.ordinary _)
  | ecall used phase operand =>
    apply mem_live image source target finish rows _ fit data hint remaining _ _ _ header (.host .ecall) (by decide)
    intro eval
    exact generated_ecall rows _ _ used phase operand data eval hint fit.ecall
  | @hint entry used =>
    apply mem_live image source target finish rows _ fit data hint remaining _ _ _ header (.host (.word entry.1)) (by cases entry.1 <;> decide)
    intro eval
    exact generated_hint run.1 used data eval (fit.hint _)
  | refresh used =>
    apply mem_live image source target finish rows _ fit data hint remaining _ _ _ header .refresh (by decide)
    intro eval
    exact generated_refresh _ _ used data eval fit.memory fit.state

variable {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)

include collected

/-- Every actual x12 length or aligned buffer read has a positively funded original physical
predecessor with its exact address, held value and incoming WRITE clock. -/
theorem read_funded {cut : ℕ} {read : Read F} (member : (cut, read) ∈ readDemand (packetRows events packets)) :
    ∃ r ∈ Counted.live (records (raw (ofExecution run routed finish data hint header remaining packets))), Counted.Covers r read := by
  let fit := heights run routed
  obtain terminal | later := WriteBoundaryBuild.compiled_read_source run.1 collected routed member finish data hint header
    (suffix image source target finish rows _ fit data hint remaining)
    (suffix_registered image source target finish rows _ fit data hint remaining)
  · exact terminal
  · obtain ⟨id, r, generated, covers⟩ := classify_predecessor run routed later
    exact ⟨r, predecessor_mem_live run routed finish data hint header remaining generated packets, covers⟩

/-- Counted routing succeeds on the full chronological read list, preserving duplicate queries. -/
theorem route_exists :
    let w := ofExecution run routed finish data hint header remaining packets
    let reads := (readDemand (packetRows (p := SP1Prime) events packets)).map Prod.snd
    ∃ requests, Counted.route? (Counted.live (records (raw w))) reads = some requests := by
  apply Counted.route?_exists
  intro read member
  obtain ⟨⟨cut, read⟩, occurs, rfl⟩ := List.mem_map.mp member
  exact read_funded run routed finish data hint header remaining collected occurs

end SP1Clean.Export.WriteMixedSourceTables
