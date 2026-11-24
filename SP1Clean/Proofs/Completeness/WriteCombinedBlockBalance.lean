import SP1Clean.Proofs.Completeness.WriteAllocationBlockBalance

/-! # Funding the complete ordered WRITE placement table

A placement on a public stream and a returned hook word both read the same fixed block
provider. Direct placements read private allocation words. Partitioning the demands only
reorders the proof of their signed sum. The physical tables keep the original row order.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics WriteAllocation
private abbrev F := ZMod SP1Prime

/-- Physical validity, signed closure and the number of all occurrences on the block bus. -/
structure CombinedBlocksChecked (source target : HostState) (groupCount wordCount : Nat)
    (placements words fixed : Table F) : Prop where
  /-- The original guarded grouped-placement component and all its local obligations. -/
  placementsValid : placements.component = groupComponent ∧ placements.Constraints ∧ placements.Guarantees
  /-- The original guarded allocation-word component and all its local obligations. -/
  wordsValid : words.component = Words.wordComponent ∧ words.Constraints ∧ words.Guarantees
  /-- The preallocated verifier component tied to the actual endpoints. -/
  fixedValid : fixed.component = blockComponent source target ∧ fixed.Constraints ∧ fixed.Guarantees
  /-- The full three physical ledgers sum to zero for every concrete block message. -/
  signed : LogUpBalanced (placements.interactionsWith blockChannel.toRaw ++ words.interactionsWith blockChannel.toRaw ++
    fixed.interactionsWith blockChannel.toRaw)
  /-- Two sites per padded placement or word and one site per verifier-fixed row. -/
  occurrences : (placements.interactionsWith blockChannel.toRaw ++ words.interactionsWith blockChannel.toRaw ++
    fixed.interactionsWith blockChannel.toRaw).length = 2 * WitnessGeneration.demandHeight groupCount +
    2 * WitnessGeneration.demandHeight wordCount + (blockTable (p := SP1Prime) (.fromEndpoints source target)).height

/-- Fund the complete group ledger, including public placements and private tag-14
placements, and every returned hint word on the original fixed provider. A read is counted
at its selected physical row each time it occurs. -/
theorem combined_block_balance (source target : HostState) (groups : List (Group F)) (rows : List (Words.Row F))
    (privateUses : List (Fin rows.length)) (publicUses returnedUses : List (Fin (blockTable (p := SP1Prime) (.fromEndpoints source target)).height))
    (hg : WitnessGeneration.demandHeight groups.length ≤ UInt64.size) (hw : WitnessGeneration.demandHeight rows.length ≤ UInt64.size)
    (hf : (blockTable (p := SP1Prime) (.fromEndpoints source target)).height < UInt64.size)
    (groupOK : ∀ g ∈ groups, g.Valid ∧ g.HonestCoordinates) (wordOK : ∀ r ∈ rows, r.Valid)
    (partition : (groups.flatMap directRequests).Perm (privateUses.map (fun i => rows[i].direct) ++
      publicUses.map (fun i => ((blockTable (p := SP1Prime) (.fromEndpoints source target)).fixedEntry i.val).payload)))
    (returnedOrder : returnedUses.map (fun i => ((blockTable (p := SP1Prime) (.fromEndpoints source target)).fixedEntry i.val).payload) =
      returnedRequests rows)
    (directOn : ∀ i ∈ privateUses, rows[i].directGate = 1)
    (fixedOn : ∀ i ∈ publicUses ++ returnedUses, ((blockTable (p := SP1Prime) (.fromEndpoints source target)).fixedEntry i.val).eligible = 1)
    (data : ProverData F) :
    let provider := blockTable (p := SP1Prime) (.fromEndpoints source target)
    let counts := ReaderCounts.counts (publicUses ++ returnedUses)
    CombinedBlocksChecked source target groups.length rows.length (groupTable groups data hg)
      (Words.wordTable (fundedWords rows privateUses) data (by rwa [fundedWords_length]))
      (provider.buildPayload blockChannel (by intros; trivial) hf (fun i => (counts[i] : F)) data) := by
  intro provider counts
  let fixedPayload := fun i : Fin provider.height => (provider.fixedEntry i.val).payload
  have updatedOK := fundedWords_valid rows privateUses wordOK
  have fixedOK := provider.buildPayload_valid blockChannel (by intros; trivial) hf _ data (fixedCounts_eligible _ fixedOn)
  have transfers := provider.buildPayload_interactions blockChannel (by intros; trivial) hf (fun i => (counts[i] : F)) data
  refine ⟨⟨rfl, groupTable_valid _ groupOK data hg⟩,⟨rfl,?_⟩,⟨rfl,fixedOK⟩,?_,?_⟩
  · apply Table.ofInputs_valid
    exact WitnessGeneration.guardedRows_all Words.Row.Valid updatedOK
  · intro msg
    rw [transfers]
    simp only [balanceOf_append,groupTable_demand groups groupOK,wordTable_demand (fundedWords rows privateUses) updatedOK]
    rw [fundedWords_returns,fundedWords_emits _ _ directOn,← returnedOrder]
    have reordered := balanceOf_perm (message := msg) (partition.map blockChannel.pulledValue)
    rw [reordered,List.map_append,balanceOf_append]
    have privatePaid := ReaderCounts.balanced blockChannel (fun i : Fin rows.length => rows[i].direct) privateUses msg
    have fixedPaid := ReaderCounts.balanced blockChannel fixedPayload (publicUses ++ returnedUses) msg
    rw [balanceOf_append] at privatePaid fixedPaid
    rw [List.map_append,balanceOf_append] at fixedPaid
    simp only [List.map_map,Function.comp_def]
    linear_combination privatePaid + fixedPaid
  · rw [transfers]
    simp only [List.length_append,groupTable_blocks,Words.wordTable_blocks (fundedWords rows privateUses) updatedOK,
      List.length_ofFn,List.length_flatMap,groupBlocks,Words.blockTraffic,List.length_cons,List.length_nil,
      List.map_const',List.sum_replicate_nat,WitnessGeneration.guardedRows_length,fundedWords_length]
    simp [Nat.mul_comm,provider]

end SP1Clean.WriteEffects.Witness
