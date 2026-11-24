import SP1Clean.Proofs.Completeness.WriteBlockTally
import SP1Clean.Proofs.Completeness.WriteFundedWords

/-! # Signed closure of the external block traffic of WRITE allocation

The grouped tag-14 guest placements, tag-14 allocation-word supplies, tag-4 allocation-word
pulls and fixed returned blocks use the original channel. Each of these three real tables
retains its complete padded inventory. Other public output and hook-request placements also
use the fixed provider and can add their own assigned counts to its same fixed rows.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- The indices record every occurrence in order. They are derived from the native run. -/
structure BlockFunding (entries : List Entry) (source target : HostState) where
  /-- Each enabled grouped query chooses an original occupied allocation word. -/
  direct : List (Fin (inputs entries).words.length)
  /-- Each occupied hook word chooses the matching eligible fixed block. -/
  returned : List (Fin (blockTable (p := SP1Prime) (.fromEndpoints source target)).height)
  /-- Clean's full padded private-placement table fits the backend row domain. -/
  groupsFit : WitnessGeneration.demandHeight (entries.flatMap Entry.directGroups).length ≤ UInt64.size
  /-- The complete historical allocation-word table fits, including the last padded position of every node. -/
  wordsFit : WitnessGeneration.demandHeight (inputs entries).words.length ≤ UInt64.size
  /-- The preallocation index can represent every row of the verifier's fixed provider. -/
  fixedFit : (blockTable (p := SP1Prime) (.fromEndpoints source target)).height < UInt64.size

variable {entries : List Entry} {source target : HostState}

/-- Actual private guest placements collected in temporal order. -/
def BlockFunding.placements (fund : BlockFunding entries source target) (data : ProverData F) :=
  groupTable (entries.flatMap Entry.directGroups) data fund.groupsFit

/-- The same complete allocation-word table with its reader-count column filled. -/
def BlockFunding.words (fund : BlockFunding entries source target) (data : ProverData F) :=
  Words.wordTable (fundedWords (inputs entries).words fund.direct) data (by rw [fundedWords_length]; exact fund.wordsFit)

/-- The verifier's registered payload component using the actual host endpoints and every physical fixed row. -/
def BlockFunding.fixed (fund : BlockFunding entries source target) (data : ProverData F) :=
  let sourceTable := blockTable (p := SP1Prime) (.fromEndpoints source target)
  let counts := ReaderCounts.counts fund.returned
  sourceTable.buildPayload blockChannel (by intros; trivial) fund.fixedFit (fun i => (counts[i] : F)) data

/-- Concatenate all four signed sites across the three actual tables, including zero-weight rows. -/
noncomputable def BlockFunding.ledger (fund : BlockFunding entries source target) (data : ProverData F) : List (Interaction F) :=
  (fund.placements data).interactionsWith blockChannel.toRaw ++ (fund.words data).interactionsWith blockChannel.toRaw ++
    (fund.fixed data).interactionsWith blockChannel.toRaw

/-- Full table constraints, component identities, and exact signed funding on the original block bus. -/
structure BlockFunding.Checked (fund : BlockFunding entries source target) (data : ProverData F) : Prop where
  /-- Every grouped query is counted at its actual original allocation word. -/
  directOrder : fund.direct.map (fun i => ((inputs entries).words[i]).direct) =
    (entries.flatMap Entry.directGroups).flatMap directRequests
  /-- All occupied returned words select their bytes at the verifier's physical endpoints. -/
  returnedOrder : fund.returned.map (fun i => ((blockTable (p := SP1Prime) (.fromEndpoints source target)).fixedEntry i.val).payload) =
    returnedRequests (inputs entries).words
  /-- The complete grouped placement table satisfies the original circuit. -/
  placements : (fund.placements data).Constraints ∧ (fund.placements data).Guarantees
  /-- The original word rows satisfy the allocation circuit with the assigned multiplicities. -/
  words : (fund.words data).Constraints ∧ (fund.words data).Guarantees
  /-- Actual independent fixed provider, with positive multiplicity only on eligible rows. -/
  fixed : (fund.fixed data).component = blockComponent source target ∧ (fund.fixed data).Constraints ∧ (fund.fixed data).Guarantees
  /-- Every individual concrete block message has zero net multiplicity. -/
  signed : LogUpBalanced (fund.ledger data)
  /-- All two-site guarded rows and each single preallocated push count toward physical capacity. -/
  occurrences : (fund.ledger data).length =
    2 * WitnessGeneration.demandHeight (entries.flatMap Entry.directGroups).length +
    2 * WitnessGeneration.demandHeight (inputs entries).words.length +
    (blockTable (p := SP1Prime) (.fromEndpoints source target)).height

/-- Every admitted native execution funds both external allocation block sources using the
same chronological collector. No semantic resource or reader-count certificate is required.
The result gives signed balance and the exact full occurrence count separately. -/
theorem native_allocation_block_balance {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    ∃ fund : BlockFunding entries source.host target.host, fund.Checked data := by
  obtain ⟨⟨direct,directOrder,directOn⟩,⟨returned,returnedOrder,returnedOn⟩⟩ := native_block_indices run readers collected
  obtain ⟨actual,built,_,_,_,_,_,honest⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  let groups := entries.flatMap Entry.directGroups
  let rows := (inputs entries).words
  let provider := blockTable (p := SP1Prime) (.fromEndpoints source.host target.host)
  let hg : WitnessGeneration.demandHeight groups.length ≤ UInt64.size := (native_direct_height run readers collected).trans (by decide)
  let hw : WitnessGeneration.demandHeight rows.length ≤ UInt64.size :=
    (WitnessGeneration.demandHeight_le_pow (native_word_capacity run readers collected)).trans (show 2^29 ≤ UInt64.size by decide)
  let hf : provider.height < UInt64.size := (admissible_fixed_heights run).1.trans_lt (by decide)
  let fund : BlockFunding entries source.host target.host := ⟨direct,returned,hg,hw,hf⟩
  let updated := fundedWords rows direct
  let tableFit : WitnessGeneration.demandHeight updated.length ≤ UInt64.size := by rw [fundedWords_length]; exact hw
  let fixedPayload := fun i : Fin provider.height => (provider.fixedEntry i.val).payload
  have groupOK := native_direct_groups_valid run readers collected
  have wordOK := fundedWords_valid rows direct honest.words
  have fixedOK := provider.buildPayload_valid blockChannel (by intros; trivial) hf _ data (fixedCounts_eligible returned returnedOn)
  have fixedTransfers := provider.buildPayload_interactions blockChannel (by intros; trivial) hf (fun i => ((ReaderCounts.counts returned)[i] : F)) data
  refine ⟨fund,directOrder,returnedOrder,groupTable_valid _ groupOK data hg,?_,⟨rfl,fixedOK⟩,?_,?_⟩
  · change (Words.wordTable updated data tableFit).Constraints ∧ (Words.wordTable updated data tableFit).Guarantees
    apply Table.ofInputs_valid
    exact WitnessGeneration.guardedRows_all Words.Row.Valid wordOK
  · intro msg
    change balanceOf ((groupTable groups data hg).interactionsWith _ ++ (Words.wordTable updated data tableFit).interactionsWith _ ++
      (provider.buildPayload blockChannel (by intros; trivial) hf (fun i => (ReaderCounts.counts returned)[i]) data).interactionsWith _) msg = 0
    rw [fixedTransfers]
    simp only [balanceOf_append,groupTable_demand groups groupOK,wordTable_demand updated wordOK]
    rw [fundedWords_returns,fundedWords_emits _ _ directOn,← directOrder,← returnedOrder]
    simp only [List.map_map,Function.comp_def]
    have privatePaid := ReaderCounts.balanced blockChannel (fun i : Fin rows.length => rows[i].direct) direct msg
    have publicPaid := ReaderCounts.balanced blockChannel fixedPayload returned msg
    rw [balanceOf_append] at privatePaid publicPaid
    change _ + (_ + _) + _ = 0
    linear_combination privatePaid + publicPaid
  · change (((groupTable groups data hg).interactionsWith _ ++ (Words.wordTable updated data tableFit).interactionsWith _ ++
      (provider.buildPayload blockChannel (by intros; trivial) hf (fun i => (ReaderCounts.counts returned)[i]) data).interactionsWith _)).length = _
    rw [fixedTransfers]
    simp only [List.length_append,groupTable_blocks,Words.wordTable_blocks updated wordOK,
      List.length_ofFn,List.length_flatMap,groupBlocks,Words.blockTraffic,List.length_cons,List.length_nil,List.map_const',List.sum_replicate_nat,
      WitnessGeneration.guardedRows_length,updated,fundedWords_length]
    simp [groups,rows,provider,Nat.mul_comm]

/-- Run the one-pass collector with no guessed block-reader counts. The completed tables
retain independently supplied immutable node/word reader counts for the queue channel. -/
theorem native_funded_block_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)
    (nodes : Semantics.HintQueue.NodeRecord F → F) (words : Semantics.HintQueue.WordRecord F → F) :
    let readers : Readers := ⟨nodes,fun _ => 0,words⟩
    ∃ entries, native? image source events readers = some entries ∧
      ∃ fund : BlockFunding entries source.host target.host, fund.Checked data := by
  intro readers
  obtain ⟨entries,collected,_,_⟩ := native_inputs run readers
  exact ⟨entries,collected,native_allocation_block_balance run readers data collected⟩

end SP1Clean.WriteEffects.Witness
