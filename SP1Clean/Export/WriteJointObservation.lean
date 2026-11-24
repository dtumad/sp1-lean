import SP1Clean.Export.WriteFundedInstallation
import SP1Clean.Export.WriteObservationReadBuild
import SP1Clean.Export.WriteMixedControlTables
import SP1Clean.Export.WriteInstalledEffectJoins
import SP1Clean.Export.WriteEndpointJoins
import SP1Clean.Export.WritePermissionCapacity
import SP1Clean.Export.WriteInstalledMetadata
import SP1Clean.Proofs.Completeness.WriteStreamTerminal
import SP1Clean.Proofs.Completeness.HintQueueFundedAllocations

/-! # One native witness for guest reads, commitment banks and funded WRITE allocations

The chronological execution supplies the immutable reader counts, the final private
queue state, the outgoing walk and its seal, and every alignment plan requested by a
guest group. The fixed stream metadata table counts the actual hook dispatches and allocation
steps. The original state bump and checkpoint padding are generated from the same execution.
This constructs all nineteen observer tables. Twenty-eight original supervisor tables and the
remaining shared-channel checks are still required for whole-assembly completeness.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteProbe AccessInventory Counted WriteSourceRegistry
open WriteEffects.Witness
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

private theorem public_read (pre : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (member : ch ∈ readProtocols) :
    (withPublicChecks pre).interactionsWith ch = pre.interactionsWith ch := by
  simp only [readProtocols,List.mem_cons,List.not_mem_nil,or_false] at member
  apply withPublicChecks_ledger
  · rcases member with rfl | rfl | rfl | rfl | rfl
    · exact readback_registered
    all_goals apply protocol_installed; simp [channels]
  · rcases member with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

private theorem public_bank (pre : EnsembleWitness (preprocessing image source target final)) (d : Bool)
    (t : Table F) (atSlot : WriteMixedHostTables.InstalledAt pre (.bank d none) t) :
    (withPublicChecks pre).interactionsWith (HostCommitChip.stateChannel d).toRaw =
      pre.interactionsWith (HostCommitChip.stateChannel d).toRaw := by
  obtain ⟨actual,here,component,_⟩ := atSlot
  apply withPublicChecks_ledger
  · apply (preprocessing image source target final).tables_channels actual.component
      (EnsembleWitness.component_mem_tables_of_mem (List.mem_of_getElem? here))
    rw [component]
    exact List.mem_cons_self
  · cases d <;> exact of_decide_eq_true rfl

/-- The three generated effect consumers surrounding the fixed stream-metadata source. -/
def effectMiddle {events : List ExecutionEvent} {entries : List Entry} {streams : WriteStreams}
    (cap : EffectFits events entries streams) (data : ProverData F) (metadata : Table F) : List (Table F) :=
  [WriteEffects.requestTable ((inputs entries).dispatches.map WriteEffects.Dispatch.request) data cap.requests,
   WriteEffects.octetTable (entries.flatMap Entry.decoderRows) data cap.decoders, metadata,
   WriteEffects.dispatchTable (inputs entries).dispatches data cap.dispatches]

/-- Exact padded demand for a buffer header, decoded word, classified request or placement handoff. -/
def effectDemandHeight {entries : List Entry} (r : Fin 4) : Nat :=
  let calls := WitnessGeneration.demandHeight (inputs entries).packets.length
  let words := WitnessGeneration.demandHeight (WriteObservations.wordProbes (inputs entries).packets)
  [calls,words,calls,words][r.val]'r.isLt

attribute [local irreducible] base preprocessing assembly withSources WriteMixedSourceTables.ofExecution

/-- One release-encodable run supplies all nineteen native observer tables, the Memory and
commitment families, the private outgoing queue state and its immutable reader counts.
The complete slice and queue-walk ledgers keep their exact physical occurrence counts. -/
noncomputable def ObservationAllocation {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) (data : ProverData F) (hint : ProverHint F) : Prop :=
    let release : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime ctx.image ctx.source ctx.target events :=
      ⟨run.1.mono (preset.trans InstalledAssembly.fixedProviderPreset_le_native),run.2⟩
    let uses := HintQueueReaders.freshDemand release.1
    let final := outgoingState (ctx := ctx) release.1
    let hints := outgoingTables (ctx := ctx) release.1 data
    let close := WriteEffects.closeTable ctx.source ctx.target events data
    ∃ (rows : List MixedCompiledRow)
      (routed : routeMixedRows? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows),
      ∃ packets, WriteObservations.packets? (policy SP1Prime ctx.image) ctx.image.program ctx.source.realize events = some packets ∧
      ∃ front : List (Table F), front.map Table.component = (tables ctx.source ctx.target).take 5 ∧
      ∃ (entries : List Entry) (collected : native? ctx.image ctx.source events uses.readers = some entries),
      let metadata := Metadata.table release.1 uses.readers collected data
      metadata.Constraints ∧ metadata.Guarantees ∧
      metadata.length = (WriteEffects.streamTable (p := SP1Prime) ctx.source.host ctx.target.host).height ∧
      ∃ s : SixTables entries ctx.source.host ctx.target.host, InstalledAssembly.MatchedWriteAllocation s data ∧ HintQueueReaders.AllocationReads s uses data ∧
        ∃ cap : EffectFits events entries (.fromEndpoints ctx.source.host ctx.target.host), cap.Realized data ∧
        ∃ plan : Table F, plan.component = WriteEffects.planComponent ∧ plan.Constraints ∧ plan.Guarantees ∧ plan.length = 512 ∧
          (∀ t ∈ hints, t.Constraints ∧ t.Guarantees) ∧ close.Constraints ∧ close.Guarantees ∧
        ∀ (header : SP1PublicIO F) (remaining : WriteMixedControlTables.Remaining ctx.image ctx.source ctx.target final),
          let fixed := WriteMixedControlTables.install release routed data remaining
          let plans := [plan,close]
          let w := WriteMixedSourceTables.ofExecution release routed final data hint header (WriteMixedHostTables.install release.1 data (WriteMixedFixedResources.install release routed data hint packets fixed)) packets
          let suffix := front ++ fundedSuffix s data (effectMiddle cap data metadata) hints plans
          ∃ reg : suffix.map Table.component = tables ctx.source ctx.target,
            let pre := build w suffix reg
            let full := withPublicChecks pre
            (∀ t ∈ (full.tables.drop (installSources w).tables.length).take front.length, t.Constraints ∧ t.Guarantees) ∧
            (∀ id, WriteMixedHostTables.InstalledAt pre id (WriteMixedHostTables.table release.1 data id)) ∧
            (∀ k, WriteMixedControlTables.InstalledAt pre k (WriteMixedControlTables.table release routed data k)) ∧
            (MixedHaltPadding.inputs ctx.source ctx.target).map (fun _ => (0 : BitVec 32)) ++ events.filterMap (hostExitAfter none) =
              [(SP1StateBoundary.haltCode ctx.source ctx.target).getD 0] ∧
            (∀ d, LogUpBalanced (full.interactionsWith (HostCommitChip.stateChannel d).toRaw)) ∧
            CheckedLedger (full.interactionsWith WritePermissionProvider.channel.toRaw) (WriteMixedPermissionLedger.occurrences events rows) ∧
            (∀ ch ∈ readProtocols, LogUpBalanced (full.interactionsWith ch)) ∧
            (∀ ch ∈ fundedProtocols, LogUpBalanced (full.interactionsWith ch) ∧
              (Balance.logUp (F := F)).fits (full.interactionsWith ch).length = true ∧ BalancedInteractions (full.interactionsWith ch)) ∧
            CheckedLedger (full.interactionsWith WriteEffects.sliceChannel.toRaw)
              (WitnessGeneration.demandHeight (WriteObservations.wordProbes (inputs entries).packets) + 512) ∧
            CheckedLedger (full.interactionsWith HostHintSnapshot.channel.toRaw)
              (2 * (HostHintSnapshot.inventory (p := SP1Prime) ctx.target.host.io.hints).height + 2) ∧
            CheckedLedger (full.interactionsWith WriteEffects.recordChannel.toRaw)
              ((WriteEffects.streamTable (p := SP1Prime) ctx.source.host ctx.target.host).height +
                3 * WitnessGeneration.demandHeight (inputs entries).dispatches.length + WitnessGeneration.demandHeight (inputs entries).nodes.length) ∧
            ∀ r : Fin 4, let ledger := full.interactionsWith (effectProtocols[r.val]'r.isLt)
              ledger.length = 2 * effectDemandHeight (entries := entries) r ∧ LogUpBalanced ledger ∧
                (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger

/-- Construct the mixed-execution tables and their shared physical ledgers from the chronological tape. -/
theorem compiled_observation_allocation {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) (data : ProverData F) (hint : ProverHint F) :
    ObservationAllocation run preset data hint := by
  unfold ObservationAllocation
  intro release uses final hints close
  obtain ⟨rows,routed,packets,observed,requests,_,hc,hq,hp,hs,hw,physical,_,_,_,_,_,_,_,install⟩ := counted_packet_tables release data hint
  let generated := WriteMixedSourceTables.compiledSource release routed data hint packets
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  let sources := live (records generated)
  let front := [Counted.table (allocated sources requests) data hc, WriteProbe.table (probes sources requests) data hq,
    WritePacket.table (batch.map fun r => WritePacket.fromHeader r.span.header) data hp,
    WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data hs, WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data hw]
  obtain ⟨entries,collected,s,paid,installFunds⟩ := installed_funded_write_allocation run.1 preset data uses.readers.nodes uses.readers.words
  let readers := uses.readers
  obtain ⟨cap,realized⟩ := native_effect_tables release.1 readers collected data
  obtain ⟨other,built,_,seen,_⟩ := native_inputs release.1 readers
  cases Option.some.inj (collected.symm.trans built)
  obtain rfl := Option.some.inj (observed.symm.trans seen)
  have funding := HintQueueReaders.freshDemand_funded release.1 data collected s
  obtain ⟨plan,planReg,planGood,planGuar,planSize,planCount,planSigned,planFit,planMatched⟩ :=
    native_slice_table release.1 readers collected s data
  obtain ⟨hintGood,hintMatch⟩ := outgoingTables_checked run.1 preset data
  obtain ⟨closeGood,closeGuar⟩ := WriteEffects.closeTable_valid release.1 data
  let metadata := Metadata.table release.1 readers collected data
  have md := Metadata.checked release.1 readers collected s cap data
  refine ⟨rows,routed,_,observed,front,physical,entries,collected,md.constraints,md.guarantees,md.height,s,paid,funding,cap,realized,
    plan,planReg,planGood,planGuar,planSize,hintGood,closeGood,closeGuar,?_⟩
  intro header remaining fixed plans w suffix
  have hh : hints.map Table.component = ((tables ctx.source ctx.target).drop 10).take 2 := rfl
  have hplans : plans.map Table.component = ((tables ctx.source ctx.target).drop 13).take 2 := by
    simp only [plans,List.map_cons,List.map_nil,planReg]; rfl
  let effects := effectMiddle cap data metadata
  have he : effects.map Table.component = ((tables ctx.source ctx.target).drop 5).take 4 := by
    simp only [effects,effectMiddle,List.map_cons,List.map_nil]; rfl
  have pfront : front.map Table.component = (tables ctx.source ctx.target).take 5 := physical
  have pe : (front ++ effects).map Table.component = (tables ctx.source ctx.target).take 9 := by
    rw [List.map_append,pfront,he]; rfl
  let tail := fundedSuffix s data effects hints plans
  have ptail : tail.map Table.component = (tables ctx.source ctx.target).drop 5 := by
    simp only [tail,fundedSuffix,List.map_append,he,hh,hplans]; rfl
  have reg : suffix.map Table.component = tables ctx.source ctx.target := by
    change (front ++ tail).map Table.component = _
    rw [List.map_append,pfront,ptail,List.take_append_drop]
  refine ⟨reg,?_⟩
  intro pre full
  obtain ⟨frontValid,banks,bankPaid,readPaid⟩ := install final header (WriteMixedFixedResources.install release routed data hint (inputs entries).packets fixed) tail ptail
  have endpoints := installed_endpoint_ledgers w suffix reg (s.groups data) plan _ _ rfl rfl rfl rfl
  refine ⟨frontValid,banks,WriteMixedControlTables.installed_at release routed data hint _ header remaining suffix reg,
    MixedHaltPadding.receipt release.1.1.2,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro d
    change LogUpBalanced ((withPublicChecks pre).interactionsWith _)
    rw [public_bank pre d _ (banks (.bank d none))]
    exact bankPaid d
  · exact WriteMixedPermissionLedger.public_checked release routed data hint (inputs entries).packets header fixed suffix reg run.1 preset
  · intro ch member
    change LogUpBalanced ((withPublicChecks pre).interactionsWith ch)
    rw [public_read pre ch member]
    exact readPaid ch member
  · have same : fundedSuffix s data (front ++ effects) hints plans = suffix := by
      simp only [suffix,fundedSuffix,effects,metadata,readers,List.append_assoc]
    have witness : withPublicChecks (build w (fundedSuffix s data (front ++ effects) hints plans)
        (fundedSuffix_registered s data (front ++ effects) hints plans pe hh hplans)) = full :=
      congrArg withPublicChecks (by congr 1)
    rw [← witness]
    exact installFunds w (front ++ effects) hints plans pe hh hplans
  · change CheckedLedger ((withPublicChecks (build w suffix reg)).interactionsWith _) _
    rw [endpoints.1]
    exact ⟨planCount,planSigned,planFit,planMatched⟩
  · change CheckedLedger ((withPublicChecks (build w suffix reg)).interactionsWith _) _
    rw [endpoints.2]
    simpa only [outgoingTables,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hintMatch
  · change CheckedLedger ((withPublicChecks (build w suffix reg)).interactionsWith _) _
    rw [installed_metadata_ledger w suffix reg metadata _ (s.nodes data) rfl rfl rfl]
    exact ⟨md.count,md.signed,md.fits,md.matched⟩
  · obtain ⟨_,_,_,hspan,hword,hrequest,hoctets⟩ := realized
    exact installed_effect_joins w suffix reg _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hspan hword hrequest hoctets

end SP1Clean.Export.WriteObservationAssembly
