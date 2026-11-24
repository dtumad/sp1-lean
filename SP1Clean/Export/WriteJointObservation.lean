import SP1Clean.Export.WriteFundedInstallation
import SP1Clean.Export.WriteObservationReadBuild
import SP1Clean.Export.WriteMixedFixedResources
import SP1Clean.Export.WriteInstalledEffectJoins

/-! # One native witness for guest reads, commitment banks and funded WRITE allocations

The chronological execution determines the five Memory observer tables and all six funded
allocation and block tables before the remaining generators run. Both public checks retain
the read, commitment and allocation traffic on these same canonically installed arrays.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteProbe AccessInventory Counted WriteSourceRegistry
open WriteEffects.Witness
private abbrev F := ZMod SP1Prime

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

/-- A released run at the fixed-provider preset supplies fourteen observer tables and the
entire original Memory and commitment families. Their fifteen channel results hold at once
on one ordered physical witness for every completion of the remaining registry slots. -/
theorem compiled_observation_allocation {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) (data : ProverData F) (hint : ProverHint F)
    (nodeReads : HintQueue.NodeRecord F → F) (wordReads : HintQueue.WordRecord F → F) :
    let release : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime ctx.image ctx.source ctx.target events :=
      ⟨run.1.mono (preset.trans InstalledAssembly.fixedProviderPreset_le_native),run.2⟩
    ∃ (rows : List MixedCompiledRow)
      (routed : routeMixedRows? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows),
      ∃ packets, WriteObservations.packets? (policy SP1Prime ctx.image) ctx.image.program ctx.source.realize events = some packets ∧
      ∃ front : List (Table F), front.map Table.component = (tables ctx.source ctx.target).take 5 ∧
      ∃ entries, native? ctx.image ctx.source events ⟨nodeReads,fun _ => 0,wordReads⟩ = some entries ∧
      ∃ s : SixTables entries ctx.source.host ctx.target.host, InstalledAssembly.MatchedWriteAllocation s data ∧
        ∃ cap : EffectFits events entries (.fromEndpoints ctx.source.host ctx.target.host), cap.Realized data ∧
        ∀ (final : HostHintQueue.State F) (header : SP1PublicIO F) (remaining : WriteMixedFixedResources.Remaining ctx.image ctx.source ctx.target final)
          (metadata : Table F) (hints plans : List (Table F)),
          metadata.component = WriteEffects.streamComponent ctx.source.host ctx.target.host →
          hints.map Table.component = ((tables ctx.source ctx.target).drop 10).take 2 →
          plans.map Table.component = ((tables ctx.source ctx.target).drop 13).take 2 →
          let w := WriteMixedSourceTables.ofExecution release routed final data hint header (WriteMixedHostTables.install release.1 data (WriteMixedFixedResources.install release routed data hint packets remaining)) packets
          let suffix := front ++ fundedSuffix s data (effectMiddle cap data metadata) hints plans
          ∃ reg : suffix.map Table.component = tables ctx.source ctx.target,
            let pre := build w suffix reg
            let full := withPublicChecks pre
            (∀ t ∈ (full.tables.drop (installSources w).tables.length).take front.length, t.Constraints ∧ t.Guarantees) ∧
            (∀ id, WriteMixedHostTables.InstalledAt pre id (WriteMixedHostTables.table release.1 data id)) ∧
            (∀ d, LogUpBalanced (full.interactionsWith (HostCommitChip.stateChannel d).toRaw)) ∧
            (∀ ch ∈ readProtocols, LogUpBalanced (full.interactionsWith ch)) ∧
            (∀ ch ∈ fundedProtocols, LogUpBalanced (full.interactionsWith ch) ∧
              (Balance.logUp (F := F)).fits (full.interactionsWith ch).length = true ∧ BalancedInteractions (full.interactionsWith ch)) ∧
            ∀ r : Fin 4, let ledger := full.interactionsWith (effectProtocols[r.val]'r.isLt)
              ledger.length = 2 * effectDemandHeight (entries := entries) r ∧ LogUpBalanced ledger ∧
                (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  intro release
  obtain ⟨rows,routed,packets,observed,requests,_,hc,hq,hp,hs,hw,physical,_,_,_,_,_,_,_,install⟩ := counted_packet_tables release data hint
  let generated := WriteMixedSourceTables.compiledSource release routed data hint packets
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  let sources := live (records generated)
  let front := [Counted.table (allocated sources requests) data hc, WriteProbe.table (probes sources requests) data hq,
    WritePacket.table (batch.map fun r => WritePacket.fromHeader r.span.header) data hp,
    WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data hs, WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data hw]
  obtain ⟨entries,collected,s,paid,installFunds⟩ := installed_funded_write_allocation run.1 preset data nodeReads wordReads
  let readers : WriteAllocation.Readers := ⟨nodeReads,fun _ => 0,wordReads⟩
  obtain ⟨cap,realized⟩ := native_effect_tables release.1 readers collected data
  obtain ⟨other,built,_,seen,_⟩ := native_inputs release.1 readers
  cases Option.some.inj (collected.symm.trans built)
  obtain rfl := Option.some.inj (observed.symm.trans seen)
  refine ⟨rows,routed,_,observed,front,physical,entries,collected,s,paid,cap,realized,?_⟩
  intro final header remaining metadata hints plans hm hh hplans w suffix
  let effects := effectMiddle cap data metadata
  have he : effects.map Table.component = ((tables ctx.source ctx.target).drop 5).take 4 := by
    simp only [effects,effectMiddle,List.map_cons,List.map_nil,hm]; rfl
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
  obtain ⟨frontValid,banks,bankPaid,readPaid⟩ := install final header (WriteMixedFixedResources.install release routed data hint (inputs entries).packets remaining) tail ptail
  refine ⟨frontValid,banks,?_,?_,?_,?_⟩
  · intro d
    change LogUpBalanced ((withPublicChecks pre).interactionsWith _)
    rw [public_bank pre d _ (banks (.bank d none))]
    exact bankPaid d
  · intro ch member
    change LogUpBalanced ((withPublicChecks pre).interactionsWith ch)
    rw [public_read pre ch member]
    exact readPaid ch member
  · have same : fundedSuffix s data (front ++ effects) hints plans = suffix := by
      simp only [suffix,fundedSuffix,effects,List.append_assoc]
    have witness : withPublicChecks (build w (fundedSuffix s data (front ++ effects) hints plans)
        (fundedSuffix_registered s data (front ++ effects) hints plans pe hh hplans)) = full :=
      congrArg withPublicChecks (by congr 1)
    rw [← witness]
    exact installFunds w (front ++ effects) hints plans pe hh hplans
  · obtain ⟨_,_,_,hspan,hword,hrequest,hoctets⟩ := realized
    exact installed_effect_joins w suffix reg _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hspan hword hrequest hoctets

end SP1Clean.Export.WriteObservationAssembly
