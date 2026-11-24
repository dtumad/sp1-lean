import SP1Clean.Export.WriteObserverSlotLedger
import SP1Clean.Export.WriteOutgoingSnapshot
import SP1Clean.Proofs.Completeness.HintQueueFixedReaders
import SP1Clean.Proofs.Completeness.WriteSlicePlans

/-! # Exact physical ledgers for the WRITE slice plans and outgoing queue walk -/

namespace SP1Clean.Export.WriteObservationAssembly

open Air.Flat Circuit Semantics Machine TraceGen FormalModel.Shard WriteEffects.Witness WriteSourceRegistry
private abbrev F := ZMod SP1Prime

variable {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime ctx.image ctx.source ctx.target events)

/-- The state sealed by the actual last queue access on this tape. -/
noncomputable def outgoingState : HostHintQueue.State F :=
  let cursor := HintQueueReaders.finalCursor run
  HostHintQueue.State.encode (events.foldl WriteAllocation.advanceQueueClock 0) cursor.2 cursor.1.size

/-- Ordered outgoing reader and singleton seal on the canonical final immutable cursor. -/
noncomputable def outgoingTables (data : ProverData F) : List (Table F) :=
  let cursor := HintQueueReaders.finalCursor run
  let hints := ctx.target.host.io.hints
  [HostHintSnapshot.tableFor cursor.1 cursor.2 hints (InstalledAssembly.admissible_hint_snapshot_fits run) data,
   HostHintSnapshot.Seal.tableFor hints (outgoingState run) data]

/-- Exact count, signed balance, field fit and active matches for one whole physical ledger. -/
structure CheckedLedger (ledger : List (Interaction F)) (count : Nat) : Prop where
  /-- Physical count including zero-weight sites. -/
  size : ledger.length = count
  /-- Every encoded value has total signed multiplicity zero. -/
  signed : LogUpBalanced ledger
  /-- The entire occurrence count fits the released field. -/
  fits : (Balance.logUp (F := F)).fits ledger.length = true
  /-- Every active occurrence has a matching occurrence of opposite sign. -/
  matched : BalancedInteractions ledger

/-- The generated immutable reader and terminal table both satisfy their local obligations.
Their actual fixed and padded rows fund the complete private walk. -/
theorem outgoingTables_checked {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) (data : ProverData F) :
    let native := run.mono (preset.trans InstalledAssembly.fixedProviderPreset_le_native)
    let tables := outgoingTables (ctx := ctx) native data
    (∀ t ∈ tables, t.Constraints ∧ t.Guarantees) ∧
      CheckedLedger (tables.flatMap (·.interactionsWith HostHintSnapshot.channel.toRaw))
        (2 * (HostHintSnapshot.inventory (p := SP1Prime) ctx.target.host.io.hints).height + 2) := by
  intro native tables
  obtain ⟨cursor,replay,reader,good,terminal,guar,count,signed,fit,matched⟩ := InstalledAssembly.compiled_outgoing_snapshot run preset data
  cases Option.some.inj (replay.symm.trans (HintQueueReaders.finalCursor_done native))
  constructor
  · intro t member
    simp only [tables,outgoingTables,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨reader,good⟩
    · exact ⟨terminal,guar⟩
  · simp only [tables,outgoingTables,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact ⟨count,signed,fit,matched⟩

/-- The group/plan and read/seal channels occur at precisely these four positions after
all private tables and both public checks have been installed. -/
theorem installed_endpoint_ledgers {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
    (w : EnsembleWitness (base image source target final)) (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)
    (groups plans reader terminal : Table F)
    (groupAt : suffix[9]? = some groups) (planAt : suffix[13]? = some plans)
    (readAt : suffix[10]? = some reader) (sealAt : suffix[11]? = some terminal) :
    let full := withPublicChecks (build w suffix reg)
    full.interactionsWith WriteEffects.sliceChannel.toRaw = groups.interactionsWith WriteEffects.sliceChannel.toRaw ++ plans.interactionsWith WriteEffects.sliceChannel.toRaw ∧
    full.interactionsWith HostHintSnapshot.channel.toRaw = reader.interactionsWith HostHintSnapshot.channel.toRaw ++ terminal.interactionsWith HostHintSnapshot.channel.toRaw := by
  exact ⟨build_pair_ledger w suffix reg WriteEffects.sliceChannel.toRaw (by simp [channels])
    (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 9 13 rfl _ _ groupAt planAt,
    build_pair_ledger w suffix reg HostHintSnapshot.channel.toRaw (by simp [channels])
    (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 10 11 rfl _ _ readAt sealAt⟩

end SP1Clean.Export.WriteObservationAssembly
