import SP1Clean.Proofs.Completeness.WriteCollectedGroups
import SP1Clean.Proofs.Completeness.WriteCombinedBlockBalance

/-! # Complete physical WRITE block balance on the native mixed timeline

Every guest read occupies one group in the shared chronological table. Private fresh words
fund tag 14. The verifier's single preallocated provider funds every public placement and
all occupied returned-hint words, including repeated hits on the same original block.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

private theorem partition (full : WriteStreams) (entries : List Entry) :
    (entries.flatMap (Entry.placementGroups full)).Perm
      (entries.flatMap Entry.directGroups ++ entries.flatMap (Entry.publicGroups full)) := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,Entry.placementGroups,List.append_assoc]
    exact (ih.append_left (e.publicGroups full) |>.append_left e.directGroups).trans
      ((List.perm_append_comm_assoc _ _ _).append_left _)

/-- All live public group requests receive genuine eligible positions of the same fixed block
source. Ignored packets retain their groups and contribute zero requests. -/
theorem native_public_indices {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    let full := WriteStreams.fromEndpoints source.host target.host
    let provider := blockTable (p := SP1Prime) full
    ∃ used : List (Fin provider.height),
      used.map (fun i => (provider.fixedEntry i.val).payload) = (entries.flatMap (Entry.publicGroups full)).flatMap directRequests ∧
      ∀ i ∈ used, (provider.fixedEntry i.val).eligible = 1 := by
  intro full provider
  apply ReaderCounts.assign
  intro b query
  obtain ⟨g,atGroup,atBlock⟩ := List.mem_flatMap.mp query
  have funded := (native_public_groups run readers collected g atGroup).2 b atBlock
  obtain ⟨i,same,live⟩ := (provider.spec_iff_fixedEntry b).mp funded
  exact ⟨i,live,same⟩

/-- The complete word-sized WRITE stream channel balances for every admitted native shard,
using one chronological placement table, one allocation-word table and one endpoint provider.
Their original component identities, validation and full physical occurrence count are
included. The execution itself fixes the groups and totals; no block-read multiplicities,
eligible positions, or stream correctness certificate are supplied by the caller. -/
theorem native_combined_block_balance {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)
    (readers : Readers) {entries : List Entry} (collected : native? image source events readers = some entries) :
    let full := WriteStreams.fromEndpoints source.host target.host
    let groups := entries.flatMap (Entry.placementGroups full)
    let rows := (inputs entries).words
    let provider := blockTable (p := SP1Prime) full
    ∃ (direct : List (Fin rows.length)) (publicReads returns : List (Fin provider.height))
      (hg : WitnessGeneration.demandHeight groups.length ≤ UInt64.size)
      (hw : WitnessGeneration.demandHeight (fundedWords rows direct).length ≤ UInt64.size) (hf : provider.height < UInt64.size),
      let counts := ReaderCounts.counts (publicReads ++ returns)
      CombinedBlocksChecked source.host target.host groups.length rows.length (groupTable groups data hg)
        (Words.wordTable (fundedWords rows direct) data hw)
        (provider.buildPayload blockChannel (by intros; trivial) hf (fun i => (counts[i] : F)) data) := by
  intro full groups rows provider
  obtain ⟨⟨direct,directOrder,directOn⟩,⟨returns,returnOrder,returnOn⟩⟩ := native_block_indices run readers collected
  obtain ⟨publicReads,publicOrder,publicOn⟩ := native_public_indices run readers collected
  obtain ⟨actual,built,_,observed,_,_,_,honest⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  have shape := partition full entries
  have allocated := native_direct_groups_valid run readers collected
  have publicChecked := native_public_groups run readers collected
  have groupOK (g : Group F) (inGroup : g ∈ groups) : g.Valid ∧ g.HonestCoordinates := by
    rcases List.mem_append.mp (shape.mem_iff.mp inGroup) with privateGroup | publicGroup
    · exact allocated g privateGroup
    · exact (publicChecked g publicGroup).1
  have separated := shape.flatMap_right directRequests
  rw [List.flatMap_append,← directOrder,← publicOrder] at separated
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have amount := (WriteObservations.packets_native_bound run.1.2 observed ticks (run.2.2.1 .readBytes)).2.1
  have hg : WitnessGeneration.demandHeight groups.length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 28) _).trans (by decide)
    rw [placementGroups_length]
    exact amount.trans (by decide)
  have hw : WitnessGeneration.demandHeight rows.length ≤ UInt64.size :=
    (WitnessGeneration.demandHeight_le_pow (native_word_capacity run readers collected)).trans (show 2^29 ≤ UInt64.size by decide)
  have hf : provider.height < UInt64.size := (admissible_fixed_heights run).1.trans_lt (by decide)
  refine ⟨direct,publicReads,returns,hg,?_,hf,combined_block_balance _ _ groups rows direct publicReads returns hg hw hf
    groupOK honest.words separated returnOrder directOn ?_ data⟩
  · rwa [fundedWords_length]
  · intro i belongs
    exact (List.mem_append.mp belongs).elim (publicOn i) (returnOn i)

/-- At the native entry point, the chronological collector needs no prior counts for block
reads. It generates all active and padded group, allocation-word and verifier-fixed block
rows from the execution, with their complete original channel in signed balance. -/
theorem native_block_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)
    (nodes : Semantics.HintQueue.NodeRecord F → F) (words : Semantics.HintQueue.WordRecord F → F) :
    let readers : Readers := ⟨nodes,fun _ => 0,words⟩
    let full := WriteStreams.fromEndpoints source.host target.host
    let provider := blockTable (p := SP1Prime) full
    ∃ entries, native? image source events readers = some entries ∧
      let groups := entries.flatMap (Entry.placementGroups full)
      let rows := (inputs entries).words
      ∃ (direct : List (Fin rows.length)) (publicReads returns : List (Fin provider.height))
        (hg : WitnessGeneration.demandHeight groups.length ≤ UInt64.size)
        (hw : WitnessGeneration.demandHeight (fundedWords rows direct).length ≤ UInt64.size) (hf : provider.height < UInt64.size),
        CombinedBlocksChecked source.host target.host groups.length rows.length (groupTable groups data hg)
          (Words.wordTable (fundedWords rows direct) data hw)
          (provider.buildPayload blockChannel (by intros; trivial) hf (fun i => ((ReaderCounts.counts (publicReads ++ returns))[i] : F)) data) := by
  intro readers full provider
  obtain ⟨entries,collected,_,_⟩ := native_inputs run readers
  exact ⟨entries,collected,native_combined_block_balance run data readers collected⟩

end SP1Clean.WriteEffects.Witness
