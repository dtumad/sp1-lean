import SP1Clean.Proofs.Completeness.WriteMetadataAvailable
import ToClean.Air.StaticReadCounts

/-! # Counted verifier-fixed metadata for the chronological WRITE observer

One preallocated table serves the actual dispatches and fresh nodes. The three physical heights
account for every metadata occurrence at the full native resource limits, including disabled
rows. The provider counts successful hook queries on its own eligible fixed rows.
-/

namespace SP1Clean.WriteEffects.Witness.Metadata

open Air.Flat Circuit WitnessGeneration Semantics Machine FormalModel.Shard TraceGen WriteAllocation

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)

/-- Original metadata provider at suffix position 7, populated from every successful endpoint query. -/
def table (data : ProverData F) : Table F :=
  (streamTable source.host target.host).countedPayload recordChannel (by intros; trivial)
    (streamTable_height_lt_uint64 source.host target.host) (records entries) (available run readers collected) data

/-- Full record-channel traffic from the three original physical positions in registry order. -/
noncomputable def ledger (provider dispatches nodes : Table F) : List (Interaction F) :=
  [provider,dispatches,nodes].flatMap (·.interactionsWith recordChannel.toRaw)

/-- Exact native fixed-table contract, including the characteristic check for all three positions. -/
structure Checked (source target : HostState) (entries : List Entry) (provider dispatches nodes : Table F) : Prop where
  /-- Verifier-owned fixed metadata circuit, including its official preallocation. -/
  registered : provider.component = streamComponent source target
  /-- The physical multiplicities satisfy the fixed table's constraints. -/
  constraints : provider.Constraints
  /-- Every local channel guarantee holds. -/
  guarantees : provider.Guarantees
  /-- Every row, including fixed padding and unrequested entries. -/
  height : provider.length = (streamTable (p := SP1Prime) source target).height
  /-- The fixed provider, three sites per dispatch, and one site per fresh node. -/
  count : (ledger provider dispatches nodes).length = (streamTable (p := SP1Prime) source target).height +
    3*demandHeight (inputs entries).dispatches.length + demandHeight (inputs entries).nodes.length
  /-- Unit demand and the counted fixed rows have exactly the same signed payload sum. -/
  signed : LogUpBalanced (ledger provider dispatches nodes)
  /-- Total physical occurrences fit the native field. -/
  fits : (Balance.logUp (F := F)).fits (ledger provider dispatches nodes).length = true
  /-- The signed and count checks imply Clean's abstract matching guarantees. -/
  matched : BalancedInteractions (ledger provider dispatches nodes)

/-- The actual funded dispatcher and allocator share one fully checked native metadata provider. -/
theorem checked (six : SixTables entries source.host target.host)
    (effects : EffectFits events entries (.fromEndpoints source.host target.host)) (data : ProverData F) :
    Checked source.host target.host entries (table run readers collected data)
      (dispatchTable (inputs entries).dispatches data effects.dispatches) (six.nodes data) := by
  let fixed := streamTable (p := SP1Prime) source.host target.host
  let provider := table run readers collected data
  let ds := dispatchTable (inputs entries).dispatches data effects.dispatches
  let ns := six.nodes data
  let bus := (recordChannel (p := SP1Prime)).toRaw
  obtain ⟨actual,built,_,_,_,number,_,good⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  obtain ⟨localOk,supplied,rows,funded⟩ := fixed.countedPayload_checked recordChannel (by intros; trivial)
    (streamTable_height_lt_uint64 source.host target.host) (records entries) (available run readers collected) data
  change (provider.interactionsWith bus).length = fixed.height at rows
  change LogUpBalanced (provider.interactionsWith bus ++ (records entries).map recordChannel.pulledValue) at funded
  have grouped : ledger provider ds ns = provider.interactionsWith bus ++ (ds.interactionsWith bus ++ ns.interactionsWith bus) := by
    simp only [ledger,List.flatMap_cons,List.flatMap_nil,List.append_nil,bus]
  have count : (ledger provider ds ns).length = fixed.height + 3*demandHeight (inputs entries).dispatches.length +
      demandHeight (inputs entries).nodes.length := by
    rw [grouped,List.length_append,rows]
    change _ + ((dispatchTable _ _ _).interactionsWith recordChannel.toRaw ++ (stepTable _ _ _).interactionsWith recordChannel.toRaw).length = _
    rw [client_count]
    omega
  have signed : LogUpBalanced (ledger provider ds ns) := by
    intro msg
    have paid := funded msg
    rw [grouped,balanceOf_append]
    change _ + balanceOf ((dispatchTable _ _ _).interactionsWith recordChannel.toRaw ++
      (stepTable _ _ _).interactionsWith recordChannel.toRaw) msg = 0
    rw [signed_clients entries good]
    rwa [balanceOf_append] at paid
  have eventsFit := run.2.2.1 .events
  rw [run.1.2.resources_events] at eventsFit
  have dispatchFit : demandHeight (inputs entries).dispatches.length ≤ 2^21 :=
    demandHeight_le_pow (number ▸ (List.countP_le_length ..).trans eventsFit)
  have nodeFit : demandHeight (inputs entries).nodes.length ≤ 2^29 :=
    demandHeight_le_pow ((native_node_count run readers collected).trans (native_word_capacity run readers collected))
  have fixedHeight : fixed.height ≤ 2^30 := (admissible_fixed_heights run).2.1
  have safe : 2^30 + 3*2^21 + 2^29 < SP1Prime := by decide
  have fits : (Balance.logUp (F := F)).fits (ledger provider ds ns).length = true := by
    simp only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n]
    omega
  have height : provider.length = fixed.height := by
    let counts (i : Fin fixed.height) : F := ((ReaderCounts.counts (fixed.requestSlots (records entries) (available run readers collected)))[i] : F)
    change (List.map _ (fixed.payloadInputs counts)).length = fixed.height
    exact (List.length_map _).trans (fixed.payloadInputs_length counts)
  exact ⟨rfl,localOk,supplied,height,count,signed,fits,Balance.logUp.balancedInteractions_of_balanced _ fits signed⟩

end SP1Clean.WriteEffects.Witness.Metadata
