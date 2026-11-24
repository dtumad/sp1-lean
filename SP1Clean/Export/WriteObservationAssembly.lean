import SP1Clean.Export.WriteSourceInstallation
import SP1Clean.Proofs.Chips.WritePacket.Ledger
import SP1Clean.Proofs.Operations.WriteProbeLedger
import SP1Clean.Proofs.Operations.WritePlacement
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Completeness.WriteStreamExecution

/-! # Physical WRITE packet and effect inputs in the native supervisor

The supervisor reads x12 and guest memory at the incoming ECALL clock. This installation
binds the physical sources, the counted version supply, packet and ordered buffer rows,
the classified requests, and the position-keyed guest bytes. The fixed stream provider depends on the two host snapshots.
The chronological consumer of the packet positions, requests and allocated queue nodes
is a further installation.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness WriteProbe Channels
open WriteSourceRegistry

private abbrev F := ZMod SP1Prime

/-- The local WRITE declarations after the read-back channel on the original sources. -/
def channels : List (RawChannel F) :=
  [versionChannel.toRaw, readChannel.toRaw, WritePacket.channel.toRaw, WriteBuffer.channel.toRaw,
   WriteBuffer.effectHeaderChannel.toRaw, WriteBuffer.wordChannel.toRaw, WriteEffects.requestChannel.toRaw,
   WriteEffects.octetsChannel.toRaw, WriteEffects.recordChannel.toRaw, WriteEffects.byteChannel.toRaw,
   WriteEffects.positionChannel.toRaw, WriteEffects.nodeByteChannel.toRaw]

/-- Packet and preprocessing components in physical order. -/
def tables (source target : HostState) : List (Component F) :=
  [ReadbackSupply.component, WriteProbe.component, WritePacket.component, WriteBuffer.spanComponent,
    WriteBuffer.wordComponent, WriteEffects.requestComponent, WriteEffects.wordComponent,
    WriteEffects.streamComponent source target, WriteEffects.laneComponent, WriteEffects.byteStepComponent]

private def protocols : List (RawChannel F) :=
  HostCallChip.channel.toRaw :: byteChannel.toRaw :: readbackChannel.toRaw :: channels

private theorem tables_registered (source target : HostState) (c : Component F) (member : c ∈ tables source target) :
    c.circuit.channels ⊆ protocols := by
  let readback := (readbackChannel (p := SP1Prime)).toRaw
  let versions := (versionChannel (p := SP1Prime)).toRaw
  let read := (readChannel (p := SP1Prime)).toRaw
  let calls := (HostCallChip.channel (p := SP1Prime)).toRaw
  let packet := (WritePacket.channel (p := SP1Prime)).toRaw
  let cursor := (WriteBuffer.channel (p := SP1Prime)).toRaw
  let header := (WriteBuffer.effectHeaderChannel (p := SP1Prime)).toRaw
  let word := (WriteBuffer.wordChannel (p := SP1Prime)).toRaw
  let request := (WriteEffects.requestChannel (p := SP1Prime)).toRaw
  let octets := (WriteEffects.octetsChannel (p := SP1Prime)).toRaw
  let record := (WriteEffects.recordChannel (p := SP1Prime)).toRaw
  let byte := (byteChannel (p := SP1Prime)).toRaw
  let lane := (WriteEffects.byteChannel (p := SP1Prime)).toRaw
  let position := (WriteEffects.positionChannel (p := SP1Prime)).toRaw
  let node := (WriteEffects.nodeByteChannel (p := SP1Prime)).toRaw
  have declarations : (tables source target).map (·.circuit.channels) =
      [[readback, versions], [versions, read], [calls, read, packet],
       [byte, byte, byte, byte, byte, byte, packet, cursor, cursor, header],
       [byte, cursor, read, cursor, word], [header, request], [word, byte, octets], [record],
       [octets, lane], [position, lane, byte, byte, record, record, node, position]] := by rfl
  have actual := List.mem_map_of_mem (f := fun t : Component F => t.circuit.channels) member
  rw [declarations] at actual
  change c.circuit.channels ⊆ [calls, byte, readback, versions, read, packet, cursor, header, word, request, octets, record, lane, position, node]
  intro ch used
  simp only [List.mem_cons, List.not_mem_nil, or_false] at actual
  rcases actual with h | h | h | h | h | h | h | h | h | h <;> rw [h] at used <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢ <;> tauto

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

private abbrev decorated := withSources image source target final

private def protocolNames := (channels.map RawChannel.name)

private theorem freshChannels :
    (channels ++ (decorated image source target final).channels).map RawChannel.name |>.Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨by decide, (decorated image source target final).unique_channel_names, ?_⟩
  intro a member b prior equal
  subst b
  change a ∈ (readbackChannel (p := SP1Prime)).name :: ((base image source target final).channels.map RawChannel.name) at prior
  have names : a ∈ protocolNames := member
  have separate : ∀ n ∈ protocolNames, n ≠ (readbackChannel (p := SP1Prime)).name ∧ n.toList.getLast? ≠ some '_' := by decide
  rcases List.mem_cons.mp prior with same | lower
  · exact (separate a names).1 same
  · apply fresh_of_registry image source target final a (separate a names).2 _ lower
    have distinct : ∀ n ∈ protocolNames, n ∉ (HostLocalCore.registry (p := SP1Prime) image source
      (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels target.sail.memorySnapshot)).map RawChannel.name := by
      simp only [HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels,
        HostFinalMemory.sourceChannels, HostFinalMemory.receiptChannels, HostFinalMemory.externalChannels,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, StaticTable.channel, StaticTable.ofRows,
        MemorySnapshot.registerTable, ProgramImage.writePermissionTable, InitialMemoryLookup.membership,
        FinalRegisterValue.membership, Channel.toRaw_name]
      decide
    exact distinct a names

private def tableNames := ["sp1.native.write_readback_supply", "sp1.native.write_probe.row",
    "sp1.native.write_packet_header", "sp1.native.write_buffer_span", "sp1.native.write_buffer_word",
    "sp1.native.write_route", "sp1.native.write_octets", "sp1.native.write_fixed_stream.source",
    "sp1.native.write_byte_lanes", "sp1.native.write_position"]

private theorem table_names (a b : HostState) : (tables a b).map (·.circuit.name) = tableNames := rfl

private theorem freshTables :
    ((decorated image source target final).tables ++ tables source.host target.host).map (·.circuit.name) |>.Nodup := by
  rw [List.map_append, table_names, List.nodup_append]
  refine ⟨(decorated image source target final).unique_names, by decide, ?_⟩
  · rw [WriteSourceRegistry.names_eq, base, HostObserved.table_names]
    simp only [HostFinalMemory.Installed, HostFinalMemory.ensemble, ClosedVerifier.install, HostFinalMemory.withReceipts,
      HostFinalMemory.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base,
      HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
      HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble]
    simp only [List.map_set, HostLocalCore.tables_names, ProtectedLocalCore.tables_names, LocalCore.tables,
      LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil, SnapshotMemoryEnsemble.registerMembership,
      StaticTable.component, StaticTable.provider, MemorySnapshot.registerTable, StaticTable.ofRows, FinalMemoryChecks.checkTables,
      FinalRegisterValue.membership, HostHintReadLocal.sourceResources, HostHintReadLocal.bankResources, HostHintQueue.source,
      HostHintQueue.sourceWord, StaticTable.payloadComponent, StaticTable.payloadProvider]
    intro a old b added equal
    subst b
    simp only [tableNames, List.mem_cons, List.not_mem_nil, or_false] at added
    rcases added with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      revert old <;> exact of_decide_eq_true rfl

private theorem protocols_registered : protocols ⊆ channels ++ (decorated image source target final).channels := by
  intro ch member
  change ch ∈ _ :: _ :: _ :: channels at member
  rcases List.mem_cons.mp member with rfl | member
  · apply List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    apply (base image source target final).tables_channels _ (List.mem_of_getElem? (original_at image source target final (.host .ecall)))
    change _ ∈ (HostCallChip.elaborated (p := SP1Prime)).channelsWithGuarantees ++ [memoryChannel.toRaw, HostCallChip.channel.toRaw]
    exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))
  rcases List.mem_cons.mp member with rfl | member
  · apply List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    apply (base image source target final).tables_channels _ (List.mem_of_getElem? (original_at image source target final (.host .ecall)))
    change _ ∈ (HostCallChip.elaborated (p := SP1Prime)).channelsWithGuarantees ++ [memoryChannel.toRaw, HostCallChip.channel.toRaw]
    rw [HostCallChip.channelsWithGuarantees_eq]
    exact List.mem_append_left _ (List.Mem.head _)
  rcases List.mem_cons.mp member with rfl | added
  · exact List.mem_append_right _ (List.Mem.head _)
  · exact List.mem_append_left _ added

/-- The installed packet and effect inputs extend the genuine supervisor at its queue
boundary. All component channels occur in the registered physical protocol. -/
def preprocessing : Ensemble F SP1PublicIO :=
  let old := decorated image source target final
  { old with
    tables := old.tables ++ tables source.host target.host
    channels := channels ++ old.channels
    unique_names := freshTables image source target final
    unique_channel_names := freshChannels image source target final
    verifier_channels := fun _ used => List.mem_append_right _ (old.verifier_channels used)
    tables_channels := by
      intro c member ch used
      rcases List.mem_append.mp member with oldRow | newRow
      · exact List.mem_append_right _ (old.tables_channels c oldRow used)
      · exact protocols_registered image source target final (tables_registered _ _ c newRow used) }

/-- The 98 supervisor components retain their positions; ten packet and effect tables follow. -/
theorem table_count : (preprocessing image source target final).tables.length = 108 := by
  change ((withSources image source target final).tables ++ tables source.host target.host).length = _
  rw [List.length_append, WriteSourceRegistry.tables_eq, List.length_mapIdx, base_length]
  rfl

/-- Read an observation component at its physical suffix position without consulting a name or a hint. -/
def slot (index : Fin 10) : TableSlot (preprocessing image source target final).tables
    (tables source.host target.host)[index.val] :=
  (TableSlot.ofIndex (tables source.host target.host) ⟨index.val, index.isLt⟩).appendRight
    (withSources image source target final).tables

/-- Check the public host endpoints used by the fixed stream provider. This stage still
exposes packet positions and node bytes to the chronological WRITE consumer. -/
def assembly : Ensemble F SP1PublicIO :=
  (WriteEffects.checker source.host target.host).install (preprocessing image source target final)

/-- The public checker enforces exact ordered endpoint deltas and representable fixed records. -/
theorem statement_iff (header : SP1PublicIO F) (heights : List ℕ) :
    (assembly image source target final).Statement .logUp header heights ↔
      (preprocessing image source target final).Statement .logUp header heights ∧
        WriteEffects.boundarySpec source.host target.host :=
  (WriteEffects.checker source.host target.host).statement_iff _
    (by change 2 < ringChar F; rw [ZMod.ringChar_zmod_n]; decide)
    (fun _ => WriteEffects.boundarySpec source.host target.host)
    (WriteEffects.checker_checks source.host target.host) header heights

/-- Every native resource-admissible mixed execution discharges the installed endpoint checker. -/
theorem statement_iff_of_execution {events : List Machine.ExecutionEvent}
    (run : FormalModel.Shard.AdmissibleExecution (ResourceLimits.native SP1Prime)
      SP1Prime image source target events) (header : SP1PublicIO F) (heights : List ℕ) :
    (assembly image source target final).Statement .logUp header heights ↔
      (preprocessing image source target final).Statement .logUp header heights := by
  rw [statement_iff, and_iff_left (WriteEffects.admissible_streams run)]

end SP1Clean.Export.WriteObservationAssembly
