import SP1Clean.Export.WriteSupplyCapacity
import SP1Clean.Proofs.Completeness.WritePacketAssembly

/-! # Compiling the first five native WRITE observer tables together

The input is the actual checked supervisor. Its read-back annotations fund the counted supplier,
which pays the probe table, which pays every actual x12 and aligned word in the mixed execution.
Source-clock bounds and totality of the deterministic route remain obligations of the supervisor
compiler. All five physical row heights are derived internally.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteProbe AccessInventory Counted WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base withSources

/-- A successful source route compiles this five-table prefix with every row constraint, five
complete raw balances and its exact native padded height vector. The request and word tables
share the original mixed execution, including empty packets and duplicate reads. -/
theorem counted_packet_tables {events : List ExecutionEvent} (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    (w : EnsembleWitness (base image source target final)) (checked : w.Constraints) (priorFit : w.InteractionsFit .logUp)
    (bounded : ∀ r ∈ live (records (raw w)), Bounded r) (data : ProverData F) :
    ∃ packets, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
      let reads := (WriteBuffer.readDemand batch).map Prod.snd
      let sourceRows := live (records (raw w))
      ∀ requests, route? sourceRows reads = some requests →
        ∃ hc hq hp hs hw, let supply := Counted.table (allocated sourceRows requests) data hc
                          let probe := WriteProbe.table (probes sourceRows requests) data hq
                          let packet := WritePacket.table (batch.map (fun r => WritePacket.fromHeader r.span.header)) data hp
                          let spans := WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data hs
                          let words := WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data hw
                          let tables := [supply, probe, packet, spans, words]
                          (∀ t ∈ tables, t.Constraints ∧ t.Guarantees) ∧
                          tables.map (·.length) = [sourceRows.length, packets.length + WriteObservations.wordProbes packets,
                            packets.length, packets.length, WriteObservations.wordProbes packets].map WitnessGeneration.demandHeight ∧
                          LogUpBalanced ((installSources w).interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw) ∧
                          LogUpBalanced (supply.interactionsWith versionChannel.toRaw ++ probe.interactionsWith versionChannel.toRaw) ∧
                          LogUpBalanced (probe.interactionsWith readChannel.toRaw ++ packet.interactionsWith readChannel.toRaw ++ words.interactionsWith readChannel.toRaw) ∧
                          LogUpBalanced (packet.interactionsWith WritePacket.channel.toRaw ++ spans.interactionsWith WritePacket.channel.toRaw) ∧
                          LogUpBalanced (spans.interactionsWith WriteBuffer.channel.toRaw ++ words.interactionsWith WriteBuffer.channel.toRaw) := by
  obtain ⟨packets, collected, hp, hs, hw, pc, pg, sc, sg, wc, wg, ph, sh, wh, headers, cursor, pays⟩ :=
    WritePacket.native_packet_buffer_tables run data
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  let reads := (WriteBuffer.readDemand batch).map Prod.snd
  let sourceRows := live (records (raw w))
  refine ⟨packets, collected, ?_⟩
  dsimp only
  intro requests routed
  let inputs := probes sourceRows requests
  have emitted : inputs.map Inputs.read = reads := (route?_spec sourceRows reads routed).2
  obtain ⟨hq, qh, readBus⟩ := pays inputs emitted
  have hc : WitnessGeneration.demandHeight (allocated sourceRows requests).length ≤ UInt64.size :=
    (supply_fits w priorFit requests).trans (by decide)
  obtain ⟨cc, cg, qc, qg, readback, versions, _, _⟩ := counted_tables w checked bounded reads routed data hc hq
  refine ⟨hc, hq, hp, hs, hw, ?_, ?_, readback, versions, readBus, headers, cursor⟩
  · intro t mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨cc, cg⟩
    · exact ⟨qc, qg⟩
    · exact ⟨pc, pg⟩
    · exact ⟨sc, sg⟩
    · exact ⟨wc, wg⟩
  · dsimp only [inputs, sourceRows] at qh
    simp only [List.map_cons, List.map_nil, supply_height, qh, ph, sh, wh]

end SP1Clean.Export.WriteObservationAssembly
