import SP1Clean.Export.WritePublicPermissions
import SP1Clean.Export.WriteEndpointJoins
import SP1Clean.Export.OrdinaryRowCapacity
import SP1Clean.Proofs.Completeness.HintReadCapacity

/-! # Exact permission-channel occurrences and characteristic fit for the native observer -/

namespace SP1Clean.Export.WriteMixedPermissionLedger
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WritePermissionProvider WriteSourceRegistry WriteProbe.AccessInventory
open WriteMixedSourceTables WriteObservationAssembly WitnessGeneration
private abbrev F := ZMod SP1Prime
private abbrev bus := (channel (p := SP1Prime)).toRaw

private noncomputable def storeCost (rows : List MixedCompiledRow) (id : InstructionChipId) : Nat :=
  demandHeight (bucket rows id).length * (original (.ordinary id)).channelWidth bus

/-- The charged height is the guard's own padded height, the height times circuit width
of each of the four STORE tables, and eight sites per padded HINT_READ word row. -/
noncomputable def occurrences (events : List ExecutionEvent) (rows : List MixedCompiledRow) : Nat :=
  let lengths := events.filterMap HintReadDemand.length?
  demandHeight (MixedPermissionDemand.bytes events rows).length + (stores.map (storeCost rows)).sum +
    8 * (demandHeight (HintReadDemand.continuing lengths) + demandHeight lengths.length)

private theorem store_width (id : InstructionChipId) : (original (.ordinary id)).channelWidth bus ≤ 8 := by
  classical
  have typed : (original (.ordinary id)).channelWidth bus ≤ InstalledAssembly.rowOccurrences (original (.ordinary id)) bus.name := by
    unfold Component.channelWidth Operations.interactionsWith InstalledAssembly.rowOccurrences
    rw [← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro interaction _ same
    exact beq_iff_eq.mpr (congrArg RawChannel.name (of_decide_eq_true same))
  exact typed.trans (InstalledAssembly.ordinary_row_width id bus.name)

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)

private theorem store_count (id : InstructionChipId) :
    ((compiledSource run routed data hint packets (.ordinary id)).interactionsWith bus).length = storeCost rows id := by
  rw [Table.interactionsWith_length,compiledSource_registered,compiledSource_later run routed data hint packets (.ordinary id) (by change 6 ≤ 7 + _; omega),
    table,InstalledInstructionTables.table_length]
  rfl

private theorem word_count (last : Bool) :
    ((compiledSource run routed data hint packets (.host (.word last))).interactionsWith bus).length =
      (demandHeight (if last then (events.filterMap HintReadDemand.length?).length else HintReadDemand.continuing (events.filterMap HintReadDemand.length?))) * 8 := by
  rw [Table.interactionsWith_length,compiledSource_registered,compiledSource_later run routed data hint packets (.host (.word last)) (by cases last <;> decide),
    table,HintReadTransfers.wordTable_length,HintReadTransfers.selected_length run.1]
  exact congrArg (_ * ·) (HintReadCapacity.widths (p := SP1Prime) last).1

private theorem guard_count : ((MixedPermissionDemand.guardTable run.1 routed data).interactionsWith bus).length =
    demandHeight (MixedPermissionDemand.bytes events rows).length := by
  rw [MixedPermissionDemand.guardTable,PermissionTables.ledger,List.length_map,guardedRows_length,PermissionTables.inputs,List.length_map]

attribute [local irreducible] base ofExecution compiledSource

/-- The entire public WRITE witness has this exact permission occurrence count at all heights. -/
theorem public_count (header : SP1PublicIO F) (remaining : WriteMixedFixedResources.Remaining image source target finish)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target) :
    let host := WriteMixedFixedResources.install run routed data hint packets remaining
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    ((withPublicChecks (build w suffix registered)).interactionsWith bus).length = occurrences events rows := by
  intro host w
  rw [public_ledger,supervisor_ledger]
  obtain ⟨guard,sources⟩ := installed_ledgers run routed data hint packets header remaining
  change ((guardSlot image source target finish).table w).interactionsWith bus = _ at guard
  change ∀ id, (raw w id).interactionsWith bus = _ at sources
  simp only [guard,sources,List.length_append,List.length_flatMap,
    store_count run routed data hint packets,word_count run routed data hint packets,guard_count run routed data,occurrences,Bool.false_eq_true,↓reduceIte]
  rw [show (fun id => storeCost rows id) = storeCost rows from rfl]
  omega

include routed in
/-- The existing fixed-provider preset pays for every padded occurrence on the native
byte-permission channel, including the separate HINT_READ continuing and final buckets. -/
theorem preset_bound {limits : ResourceLimits} (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) : occurrences events rows < SP1Prime := by
  have callLimit : limits.events ≤ 2^21 := preset.1
  have writeLimit : limits.writeBytes ≤ 2^24 := preset.2.2.2.1
  have count := execution.work.1
  obtain ⟨_,found,total⟩ := admissibleExecution_routeMixedRows execution
  cases Option.some.inj (found.symm.trans routed)
  have guard := MixedPermissionDemand.byte_count execution routed
  have guardHeight : demandHeight (MixedPermissionDemand.bytes events rows).length ≤ 2^25 := demandHeight_le_pow (by omega)
  have site (id : InstructionChipId) : storeCost rows id ≤ 2^21 * 8 := by
    apply Nat.mul_le_mul _ (store_width id)
    apply demandHeight_le_pow
    have len := (EventBuckets.length_le (rows.filterMap MixedCompiledRow.ordinaryObservation?) id).trans (List.length_filterMap_le ..)
    change (EventBuckets.ofChronological _ _).length ≤ _
    omega
  have allStores := List.sum_le_sum (l := stores) (f := storeCost rows) (g := fun _ => 2^21 * 8) (fun id _ => site id)
  have host := (HintReadCapacity.demand_bounds execution.1.2).1
  have spent := execution.2.2.1 .writeBytes
  change executionResources _ _ _ events .writeBytes ≤ limits.writeBytes at spent
  change _ ≤ 4 * (2^21 * 8) at allStores
  dsimp only [occurrences]
  unfold SP1Prime
  omega

/-- The public witness has all four native permission checks at the installed preset. -/
theorem public_checked (header : SP1PublicIO F) (remaining : WriteMixedFixedResources.Remaining image source target finish)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target)
    {limits : ResourceLimits} (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) :
    let host := WriteMixedFixedResources.install run routed data hint packets remaining
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    CheckedLedger ((withPublicChecks (build w suffix registered)).interactionsWith bus) (occurrences events rows) := by
  intro host w
  let ledger := (withPublicChecks (build w suffix registered)).interactionsWith bus
  have count : ledger.length = occurrences events rows := public_count run routed data hint packets header remaining suffix registered
  have signed : LogUpBalanced ledger := public_balanced run routed data hint packets header remaining suffix registered
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simp only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n,count]
    exact preset_bound routed execution preset
  exact ⟨count,signed,fit,Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

end SP1Clean.Export.WriteMixedPermissionLedger
