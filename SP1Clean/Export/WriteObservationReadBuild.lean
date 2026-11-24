import SP1Clean.Export.WriteMixedSupplyBounds
import SP1Clean.Export.WriteMixedHostData
import SP1Clean.Export.WriteInstalledReadBalances
import SP1Clean.Proofs.Completeness.WritePacketAssembly

/-! # Compiling the first five native WRITE observer tables together

A released mixed execution generates its original Memory sources and all five read observer
tables. Their actual positive predecessors pay every x12 and aligned buffer read. The proof
derives the source route, physical heights, clock bounds and channel balances from that run.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteProbe AccessInventory Counted WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot}

attribute [local irreducible] base withSources

/-- The genuine released mixed run constructs the five native read tables with their complete raw
balances and exact native padded height vector. The completed five-table block installs unchanged
into the original supervisor with its generated commitment and ordinary observation tables. -/
theorem counted_packet_tables {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    (data : ProverData F) (hint : ProverHint F) :
    ∃ (rows : List MixedCompiledRow)
      (compiled : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows),
      ∃ packets, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      let generated := WriteMixedSourceTables.compiledSource run compiled data hint packets
      let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
      let reads := (WriteBuffer.readDemand batch).map Prod.snd
      let sourceRows := live (records generated)
      ∃ requests, route? sourceRows reads = some requests ∧
      ∃ hc hq hp hs hw,
        let supply := Counted.table (allocated sourceRows requests) data hc
        let probe := WriteProbe.table (probes sourceRows requests) data hq
        let packet := WritePacket.table (batch.map (fun r => WritePacket.fromHeader r.span.header)) data hp
        let spans := WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data hs
        let words := WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data hw
        let block := [supply, probe, packet, spans, words]
        block.map (·.component) = (tables source target).take 5 ∧
        (∀ t ∈ block, t.Constraints ∧ t.Guarantees) ∧
        block.map (·.length) = [sourceRows.length, packets.length + WriteObservations.wordProbes packets,
          packets.length, packets.length, WriteObservations.wordProbes packets].map WitnessGeneration.demandHeight ∧
        LogUpBalanced (AccessInventory.ledger generated (WriteMixedSourceTables.compiledSource_registered run compiled data hint packets) supply) ∧
        LogUpBalanced (supply.interactionsWith versionChannel.toRaw ++ probe.interactionsWith versionChannel.toRaw) ∧
        LogUpBalanced (probe.interactionsWith readChannel.toRaw ++ packet.interactionsWith readChannel.toRaw ++ words.interactionsWith readChannel.toRaw) ∧
        LogUpBalanced (packet.interactionsWith WritePacket.channel.toRaw ++ spans.interactionsWith WritePacket.channel.toRaw) ∧
        LogUpBalanced (spans.interactionsWith WriteBuffer.channel.toRaw ++ words.interactionsWith WriteBuffer.channel.toRaw) ∧
        ∀ (final : HostHintQueue.State F) (header : SP1PublicIO F)
          (remaining : WriteMixedHostTables.Remaining image source target final)
          (tail : List (Table F)) (registered : tail.map (·.component) = (tables source target).drop 5),
          let w := WriteMixedSourceTables.ofExecution run compiled final data hint header (WriteMixedHostTables.install run.1 data remaining) packets
          let full := build w (block ++ tail) (by
            rw [List.map_append, show block.map (·.component) = (tables source target).take 5 from rfl,
              registered, List.take_append_drop])
          (∀ t ∈ (full.tables.drop (installSources w).tables.length).take block.length, t.Constraints ∧ t.Guarantees) ∧
            (∀ id, WriteMixedHostTables.InstalledAt full id (WriteMixedHostTables.table run.1 data id)) ∧
            ∀ ch ∈ readProtocols, LogUpBalanced (full.interactionsWith ch) := by
  obtain ⟨rows, compiled, _⟩ := admissibleExecution_routeMixedRows run.1
  obtain ⟨packets, collected, hp, hs, hw, pc, pg, sc, sg, wc, wg, ph, sh, wh, headers, cursor, pays⟩ :=
    WritePacket.native_packet_buffer_tables run.1 data
  refine ⟨rows, compiled, packets, collected, ?_⟩
  let generated := WriteMixedSourceTables.compiledSource run compiled data hint packets
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  let reads := (WriteBuffer.readDemand batch).map Prod.snd
  let sourceRows := live (records generated)
  obtain ⟨requests, routed⟩ := WriteMixedSourceTables.compiled_route_exists run compiled data hint collected
  refine ⟨requests, routed, ?_⟩
  let inputs := probes sourceRows requests
  have emitted : inputs.map Inputs.read = reads := (route?_spec sourceRows reads routed).2
  obtain ⟨hq, qh, readBus⟩ := pays inputs emitted
  have hc : WitnessGeneration.demandHeight (allocated sourceRows requests).length ≤ UInt64.size :=
    by simpa only [Counted.allocated, List.length_ofFn] using WriteMixedSourceTables.compiled_supply_fit run compiled data hint packets
  obtain ⟨cc, cg, qc, qg, readback, versions, _, _⟩ := physical_tables generated
    (WriteMixedSourceTables.compiledSource_registered run compiled data hint packets)
    (fun id => (WriteMixedSourceTables.compiledSource_valid run compiled data hint packets id).1)
    (WriteMixedSourceTables.compiled_bounded run compiled data hint packets) reads routed data hc hq
  let supply := Counted.table (allocated sourceRows requests) data hc
  let probe := WriteProbe.table inputs data hq
  let packet := WritePacket.table (batch.map (fun r => WritePacket.fromHeader r.span.header)) data hp
  let spans := WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data hs
  let words := WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data hw
  let block := [supply, probe, packet, spans, words]
  have valid : ∀ t ∈ block, t.Constraints ∧ t.Guarantees := by
    intro t mem
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨cc, cg⟩
    · exact ⟨qc, qg⟩
    · exact ⟨pc, pg⟩
    · exact ⟨sc, sg⟩
    · exact ⟨wc, wg⟩
  refine ⟨hc, hq, hp, hs, hw, rfl, valid, ?_, readback, versions, readBus, headers, cursor, ?_⟩
  · dsimp only [inputs, sourceRows, generated] at qh
    simp only [List.map_cons, List.map_nil, supply_height, qh, ph, sh, wh]
  · intro final header remaining tail registered w full
    have paid : LogUpBalanced (AccessInventory.ledger (raw w) (raw_registered w) supply) := by
      rw [ledger_records, WriteMixedSourceTables.compiled_records run compiled data hint packets final header (WriteMixedHostTables.install run.1 data remaining)]
      rwa [ledger_records] at readback
    have attached : LogUpBalanced ((installSources w).interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw) :=
      fun msg => (balanceOf_perm (installed_readback_perm w supply)).trans (paid msg)
    exact ⟨compiled_read_constraints w block tail rfl valid registered,
      WriteMixedHostTables.installed_at run compiled data hint header remaining packets (block ++ tail) _,
      compiled_read_balances w supply probe packet spans words rfl attached versions readBus headers cursor tail registered⟩

end SP1Clean.Export.WriteObservationAssembly
