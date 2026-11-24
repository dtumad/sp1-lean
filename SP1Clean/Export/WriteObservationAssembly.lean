import SP1Clean.Export.WriteSourceInstallation
import SP1Clean.Native.Operations.HintQueueSeal
import SP1Clean.Proofs.Chips.WritePacket.Ledger
import SP1Clean.Proofs.Operations.WriteProbeLedger
import SP1Clean.Proofs.Operations.WriteDispatch
import SP1Clean.Proofs.Operations.WriteGroup
import SP1Clean.Native.Operations.WriteCursorBoundary
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Completeness.WriteStreamExecution

/-! # Physical WRITE packet and effect inputs in the native supervisor

The supervisor reads x12 and guest memory at the incoming ECALL clock. This installation
binds the physical sources, the counted version supply, packet and ordered buffer rows,
the classified requests, and the chronological placement of every observed word. Public endpoints
fix the stream blocks, hook metadata and all four final positions. The outgoing queue walk
checks the target hint transcript; allocation of fresh nodes during WRITE is a separate obligation.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness WriteProbe Channels
open WriteSourceRegistry
open scoped Classical

private abbrev F := ZMod SP1Prime

/-- The local WRITE declarations after the read-back channel on the original sources. -/
def channels : List (RawChannel F) :=
  [versionChannel.toRaw, readChannel.toRaw, WritePacket.channel.toRaw, WriteBuffer.channel.toRaw,
   WriteBuffer.effectHeaderChannel.toRaw, WriteBuffer.wordChannel.toRaw, WriteEffects.requestChannel.toRaw,
   WriteEffects.octetsChannel.toRaw, WriteEffects.recordChannel.toRaw, WriteEffects.positionChannel.toRaw,
   HostHintSnapshot.channel.toRaw, WriteEffects.cursorChannel.toRaw, WriteEffects.queueEffectChannel.toRaw,
   WriteEffects.sliceChannel.toRaw, WriteEffects.blockChannel.toRaw, WriteEffects.closeChannel.toRaw]

/-- Packet and preprocessing components in physical order. -/
def tables (source target : ExecutionSnapshot) : List (Component F) :=
  [ReadbackSupply.component, WriteProbe.component, WritePacket.component, WriteBuffer.spanComponent,
    WriteBuffer.wordComponent, WriteEffects.requestComponent, WriteEffects.wordComponent,
    WriteEffects.streamComponent source.host target.host, WriteEffects.dispatchComponent, WriteEffects.groupComponent,
    HostHintSnapshot.component target.host.io.hints, HostHintSnapshot.Seal.component target.host.io.hints,
    WriteEffects.blockComponent source.host target.host, WriteEffects.planComponent, WriteEffects.closeComponent source target]

private def protocols : List (RawChannel F) :=
  HostCallChip.channel.toRaw :: byteChannel.toRaw :: readbackChannel.toRaw :: HostHintQueue.nodeChannel.toRaw ::
  HostHintQueue.wordChannel.toRaw :: HostHintQueue.stateChannel.toRaw :: channels

/-- Channel registration slots for every entry of the physical suffix. Entries retain
their original order and duplicate channel declarations. -/
private def protocolSlots : List (List (Fin 22)) :=
  [[2,6],[6,7],[0,7,8],[1,1,1,1,1,1,8,9,9,10],[1,9,7,9,11],[10,12],[11,1,13],[14],
   [12,17,1,1,1,1,14,14,14,15,14,18,15,17],[13,19,15,20,20,20,15],
   [16,3,4,16,3,4],[5,16,5,16],[20],[19],[17,21]]

private def registeredChannel (i : Fin 22) : RawChannel F := protocols[i.val]'(by exact i.isLt)

private theorem suffix_channels (source target : ExecutionSnapshot) :
    (tables source target).map (·.circuit.channels) = protocolSlots.map (List.map registeredChannel) := by
  rfl

private theorem tables_registered (source target : ExecutionSnapshot) (c : Component F) (member : c ∈ tables source target) :
    c.circuit.channels ⊆ protocols := by
  have found := List.mem_map_of_mem (f := fun t : Component F => t.circuit.channels) member
  rw [suffix_channels] at found
  obtain ⟨slots,_,declaration⟩ := List.mem_map.mp found
  intro ch used
  rw [← declaration] at used
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp used
  exact List.getElem_mem ..

/-- All new effect and outgoing-queue rows have no Clean lookup operations. This is the
suffix after the original seven physical packet, classifier and decoder components. -/
theorem effect_lookupFree (source target : ExecutionSnapshot) : LookupFree ((tables source target).drop 7) := by
  change LookupFree [WriteEffects.streamComponent source.host target.host,WriteEffects.dispatchComponent,WriteEffects.groupComponent,
    HostHintSnapshot.component target.host.io.hints,HostHintSnapshot.Seal.component target.host.io.hints,
    WriteEffects.blockComponent source.host target.host,WriteEffects.planComponent,WriteEffects.closeComponent source target]
  simp only [LookupFree.cons_iff,LookupFree.nil,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals apply Component.lookups_eq_nil_of_main; intro input offset
  · rfl
  · exact Guarded.main_lookups WriteEffects.dispatchCircuit WriteEffects.dispatchGuardSupported input offset
  · exact Guarded.main_lookups WriteEffects.groupCircuit WriteEffects.groupGuardSupported input offset
  · simp only [HostHintSnapshot.component,HostHintSnapshot.circuit,HostHintSnapshot.main,circuit_norm,Operations.lookups]
  · simp only [HostHintSnapshot.Seal.component,HostHintSnapshot.Seal.circuit,HostHintSnapshot.Seal.main,circuit_norm,Operations.lookups]
  · rfl
  · rfl
  · simp only [WriteEffects.closeComponent,WriteEffects.closeCircuit,WriteEffects.closeMain,AddressSum.circuit,AddressSum.main,
      WordRangeCheck.circuit,WordRangeCheck.main,Gadgets.ToBits.rangeCheck,Gadgets.toBits,Gadgets.ToBits.main,Gadgets.Equality.main,Operations.lookups,circuit_norm]

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

private def packetTableNames := ["sp1.native.write_readback_supply", "sp1.native.write_probe.row",
    "sp1.native.write_packet_header", "sp1.native.write_buffer_span", "sp1.native.write_buffer_word",
    "sp1.native.write_route", "sp1.native.write_octets", "sp1.native.write_fixed_stream.source",
    "sp1.native.write_chronological_dispatch", "sp1.native.write_word_placement"]

private def queueTableNames := [HostHintSnapshot.tableName, HostHintSnapshot.Seal.name]

private def groupedSourceNames := ["sp1.native.write_stream_blocks.source", "sp1.native.write_slice_plan.source", "sp1.native.write_output_terminal"]

private def tableNames := packetTableNames ++ queueTableNames ++ groupedSourceNames

private theorem table_names (a b : ExecutionSnapshot) : (tables a b).map (·.circuit.name) = tableNames := rfl

-- Unfold the supervisor once per family, keeping physical names independent of the endpoints.
local macro "supervisor_names" : tactic => `(tactic|
  (rw [WriteSourceRegistry.names_eq, base, HostObserved.table_names]
   simp only [HostFinalMemory.Installed, HostFinalMemory.ensemble, ClosedVerifier.install, HostFinalMemory.withReceipts,
      HostFinalMemory.withRegisters, FinalReceiptEnsemble.install, Ensemble.replaceComponent, HostFinalMemory.base,
      HostHintQueueBoundary.ensemble, HaltPadding.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
      HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble]
   simp only [List.map_set, HostLocalCore.tables_names, ProtectedLocalCore.tables_names, LocalCore.tables,
      LocalCore.afterSourceTables, List.map_append, List.map_cons, List.map_nil, SnapshotMemoryEnsemble.registerMembership,
      StaticTable.component, StaticTable.provider, MemorySnapshot.registerTable, StaticTable.ofRows, FinalMemoryChecks.checkTables,
      FinalRegisterValue.membership, HostHintReadLocal.sourceResources, HostHintReadLocal.bankResources, HostHintQueue.source,
      HostHintQueue.sourceWord, StaticTable.payloadComponent, StaticTable.payloadProvider]))

private theorem packet_names_disjoint :
    List.Disjoint ((decorated image source target final).tables.map (·.circuit.name)) packetTableNames := by
  supervisor_names
  intro a old member
  simp only [packetTableNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert old <;> exact of_decide_eq_true rfl

private theorem queue_names_disjoint :
    List.Disjoint ((decorated image source target final).tables.map (·.circuit.name)) queueTableNames := by
  supervisor_names
  intro a old member
  simp only [queueTableNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> revert old <;> exact of_decide_eq_true rfl

private theorem grouped_names_disjoint :
    List.Disjoint ((decorated image source target final).tables.map (·.circuit.name)) groupedSourceNames := by
  supervisor_names
  intro a old member
  simp only [groupedSourceNames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> revert old <;> exact of_decide_eq_true rfl

private theorem freshTables :
    ((decorated image source target final).tables ++ tables source target).map (·.circuit.name) |>.Nodup := by
  rw [List.map_append, table_names, List.nodup_append']
  exact ⟨(decorated image source target final).unique_names, by decide,
    List.disjoint_append_right.mpr ⟨List.disjoint_append_right.mpr ⟨packet_names_disjoint image source target final,
      queue_names_disjoint image source target final⟩,grouped_names_disjoint image source target final⟩⟩

private theorem protocols_registered : protocols ⊆ channels ++ (decorated image source target final).channels := by
  intro ch member
  change ch ∈ _ :: _ :: _ :: _ :: _ :: _ :: channels at member
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
  · have original (q : RawChannel F) (h : q ∈ HostFinalMemory.sourceChannels target.sail.memorySnapshot) :
        q ∈ (base image source target final).channels := by
      change _ ∈ _ ++ [_]
      apply List.mem_append_left
      change _ ∈ (_ ++ [_]) ++ [_]
      apply List.mem_append_left _ (List.mem_append_left _ ?_)
      change _ ∈ _ ++ [_]
      apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp added with rfl | added
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (original _ (by simp [HostFinalMemory.sourceChannels])))
    rcases List.mem_cons.mp added with rfl | added
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (original _ (by simp [HostFinalMemory.sourceChannels])))
    rcases List.mem_cons.mp added with rfl | added
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (original _ (by simp [HostFinalMemory.sourceChannels])))
    exact List.mem_append_left _ added

/-- The installed packet and effect inputs extend the genuine supervisor at its queue
boundary. All component channels occur in the registered physical protocol. -/
def preprocessing : Ensemble F SP1PublicIO :=
  let old := decorated image source target final
  { old with
    tables := old.tables ++ tables source target
    channels := channels ++ old.channels
    unique_names := freshTables image source target final
    unique_channel_names := freshChannels image source target final
    verifier_channels := fun _ used => List.mem_append_right _ (old.verifier_channels used)
    tables_channels := by
      intro c member ch used
      rcases List.mem_append.mp member with oldRow | newRow
      · exact List.mem_append_right _ (old.tables_channels c oldRow used)
      · exact protocols_registered image source target final (tables_registered _ _ c newRow used) }

/-- The 98 supervisor components retain their positions; the packet, effect and outgoing queue tables follow. -/
theorem table_count : (preprocessing image source target final).tables.length = 113 := by
  change ((withSources image source target final).tables ++ tables source target).length = _
  rw [List.length_append, WriteSourceRegistry.tables_eq, List.length_mapIdx, base_length]
  rfl

/-- Read an observation component at its physical suffix position without consulting a name or a hint. -/
def slot (index : Fin 15) : TableSlot (preprocessing image source target final).tables
    (tables source target)[index.val] :=
  (TableSlot.ofIndex (tables source target) ⟨index.val, index.isLt⟩).appendRight
    (withSources image source target final).tables

/-- The same queue snapshot and seal registrations occupy original physical slots 108 and 109. -/
theorem queue_slots :
    (preprocessing image source target final).tables[108]? = some (HostHintSnapshot.component target.host.io.hints) ∧
    (preprocessing image source target final).tables[109]? = some (HostHintSnapshot.Seal.component target.host.io.hints) := by
  have size : (decorated image source target final).tables.length = 98 := by
    rw [decorated,WriteSourceRegistry.tables_eq,List.length_mapIdx,base_length]
  change (_ ++ tables source target)[108]? = _ ∧ (_ ++ tables source target)[109]? = _
  simp only [List.getElem?_append_right (by omega : (decorated image source target final).tables.length ≤ 108),
    List.getElem?_append_right (by omega : (decorated image source target final).tables.length ≤ 109),size]
  exact ⟨rfl,rfl⟩

/-- The public verifier emits the initial cursor and consumes the expected final ticket.
The singleton close table checks the intervening physical terminal cursor. -/
def withCursors : Ensemble F SP1PublicIO :=
  (WriteEffects.cursorEndpoint source target).withInteractions (preprocessing image source target final) (by
    intro ch used
    change ch ∈ [WriteEffects.closeChannel.toRaw,WriteEffects.cursorChannel.toRaw] at used
    rcases List.mem_cons.mp used with rfl | rest
    · exact List.mem_append_left _ (by simp [channels])
    · obtain rfl := List.mem_singleton.mp rest
      exact List.mem_append_left _ (by simp [channels]))

/-- The public verifier physically emits and consumes these two fixed receipts, including
when no WRITE occurs. Every pre-existing verifier occurrence retains its order. -/
theorem withCursors_ledger (env : Environment F) (ch : RawChannel F) :
    (withCursors image source target final).verifierOperations.interactionValuesWith ch env =
      (preprocessing image source target final).verifierOperations.interactionValuesWith ch env ++
      [WriteEffects.cursorChannel.pushedValue (WriteEffects.initialCursor source.clock),
       WriteEffects.closeChannel.pulledValue (WriteEffects.finalCursor target.clock (.fromEndpoints source.host target.host))].filter
        (fun e => decide (e.channel = ch)) := by
  simp only [withCursors,ClosedVerifier.withInteractions,Ensemble.verifierOperations,Verifier.Program.andThen_values]
  congr 1
  change (WriteEffects.cursorEndpoint source target).emit.circuitOperations.interactionValuesWith ch env = _
  rw [ClosedVerifier.emit_values]
  exact WriteEffects.cursorBoundary_values _ _ 0 _ ch

/-- Install both public stream consistency and the actual two cursor occurrences. -/
def assembly : Ensemble F SP1PublicIO :=
  (WriteEffects.checker source.host target.host).install (withCursors image source target final)

/-- The public checker enforces exact ordered endpoint deltas and representable fixed records. -/
theorem statement_iff (header : SP1PublicIO F) (heights : List ℕ) :
    (assembly image source target final).Statement .logUp header heights ↔
      (withCursors image source target final).Statement .logUp header heights ∧
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
      (withCursors image source target final).Statement .logUp header heights := by
  rw [statement_iff, and_iff_left (WriteEffects.admissible_streams run)]

/-- At the shard boundary the public target queue is rebased to the following shard's canonical
incoming representation. The seal row supplies the actual last access clock and both private
pointers. The public statement needs only the two complete snapshots and program image. -/
def native (image : ProgramImage) (source target : ExecutionSnapshot) : Ensemble F SP1PublicIO :=
  assembly image source target (SP1Clean.HostHintQueueBoundary.initial target.host.io.hints)

end SP1Clean.Export.WriteObservationAssembly
