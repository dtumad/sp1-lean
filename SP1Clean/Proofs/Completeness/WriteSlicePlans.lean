import SP1Clean.Proofs.Completeness.WriteAllocationSix
import SP1Clean.Proofs.Completeness.WriteEffectTables
import ToClean.Air.StaticReadCounts
import ToClean.Air.GuardedLedger

/-! # Fixed alignment plans for the actual native WRITE placement table

The 352 legal guest windows occupy 512 fixed rows. Each physical guest group makes one
plan request, even when its byte window is empty. Repeated plans count at the same
fixed row and every inactive group still contributes to the field occurrence count.
-/

namespace SP1Clean.WriteEffects.Witness
open Air.Flat Circuit Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- The original verifier-fixed plan table, funded from the actual guest groups on the
complete mixed execution. The signed ledger and count use the very same placement table
that funds external stream blocks and receives the decoded guest octets. -/
theorem native_slice_table {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)
    (s : SixTables entries source.host target.host) (data : ProverData F) :
    ∃ plans : Table F, plans.component = planComponent ∧ plans.Constraints ∧ plans.Guarantees ∧
      plans.length = 512 ∧ let ledger := (s.groups data).interactionsWith sliceChannel.toRaw ++ plans.interactionsWith sliceChannel.toRaw
      ledger.length = WitnessGeneration.demandHeight (WriteObservations.wordProbes (inputs entries).packets) + 512 ∧
      LogUpBalanced ledger ∧ (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  let full := WriteStreams.fromEndpoints source.host target.host
  let groups := entries.flatMap (Entry.placementGroups full)
  let provider := planTable (p := SP1Prime)
  have height : provider.height = 512 := planTable_height
  have bounded : provider.height < UInt64.size := height.trans_lt (by decide)
  have available (plan : SlicePlan F) (used : plan ∈ groups.map Group.plan) : provider.Spec plan := by
    obtain ⟨g,member,rfl⟩ := List.mem_map.mp used
    obtain ⟨e,_,placed⟩ := List.mem_flatMap.mp member
    exact e.placement_plan full placed
  let plans := provider.countedPayload sliceChannel (by intros; trivial) bounded (groups.map Group.plan) available data
  obtain ⟨valid,guar,count,funded⟩ := provider.countedPayload_checked sliceChannel (by intros; trivial) bounded
    (groups.map Group.plan) available data
  have pf : plans.component = planComponent := rfl
  have rows : plans.length = 512 := (provider.buildPayload_length ..).trans height
  refine ⟨plans,pf,valid,guar,rows,?_⟩
  intro ledger
  have groupRows := groupTable_plans groups data s.groupFit
  have order : groups.length = WriteObservations.wordProbes (inputs entries).packets := placementGroups_length full entries
  have total : ledger.length = WitnessGeneration.demandHeight (WriteObservations.wordProbes (inputs entries).packets) + 512 := by
    change ((groupTable groups data s.groupFit).interactionsWith sliceChannel.toRaw ++ plans.interactionsWith sliceChannel.toRaw).length = _
    rw [List.length_append,groupRows,List.length_map,WitnessGeneration.guardedRows_length,order,count,height]
  have signed : LogUpBalanced ledger := by
    intro msg
    change balanceOf ((groupTable groups data s.groupFit).interactionsWith sliceChannel.toRaw ++ plans.interactionsWith sliceChannel.toRaw) msg = 0
    rw [balanceOf_append,groupRows,WitnessGeneration.guarded_pull_sum,add_comm,← balanceOf_append]
    exact funded msg
  obtain ⟨other,built,_,seen,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  obtain ⟨packets,observed,_,_,small⟩ := admissible_placement_heights run (.refl _)
  cases Option.some.inj (seen.symm.trans observed)
  have below : ledger.length < SP1Prime := by rw [total]; exact (Nat.add_le_add_right small 512).trans_lt (by decide)
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n] using below
  exact ⟨total,signed,fit,Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

end SP1Clean.WriteEffects.Witness
