import SP1Clean.Proofs.Completeness.WriteWitnessAllocationAssembly

/-! # Count bounds for the three internal allocation ledgers

All allocated rows count, including the zero outgoing cursor on a final word and both cursor
sites of each disabled row. The native historical bound pays for every occurrence. Clean's
LogUp soundness theorem therefore yields matching active messages on all three joins.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation

private abbrev F := ZMod SP1Prime

/-- Exact physical occurrence counts on the two cursor joins and the intervening contents join. -/
theorem allocation_occurrences (r : Inputs) (data : ProverData F) (hc hn hs hw) :
    let call := openTable r.openings data hc
    let node := stepTable r.nodes data hn
    let seed := Words.seedTable r.contents data hs
    let body := Words.wordTable r.words data hw
    (call.interactionsWith WriteAllocation.cursorChannel.toRaw ++ node.interactionsWith WriteAllocation.cursorChannel.toRaw).length =
        2 * WitnessGeneration.demandHeight r.openings.length + 2 * WitnessGeneration.demandHeight r.nodes.length ∧
      (node.interactionsWith contentsChannel.toRaw ++ seed.interactionsWith contentsChannel.toRaw).length =
        WitnessGeneration.demandHeight r.nodes.length + WitnessGeneration.demandHeight r.contents.length ∧
      (seed.interactionsWith Words.cursorChannel.toRaw ++ body.interactionsWith Words.cursorChannel.toRaw).length =
        WitnessGeneration.demandHeight r.contents.length + 2 * WitnessGeneration.demandHeight r.words.length := by
  dsimp only
  simp only [List.length_append,openTable_cursors,stepTable_cursors,stepTable_contents,Words.seedTable_contents,
    Words.seedTable_cursors,Words.wordTable_cursors,List.length_map,List.length_flatMap,openCursors,stepCursors,
    Words.seedCursors,Words.wordCursors,List.length_cons,List.length_nil,List.map_const',List.sum_replicate_nat,
    WitnessGeneration.guardedRows_length]
  simp [Nat.mul_comm]

private theorem checked_balance (ledger : List (Interaction F)) (small : ledger.length < SP1Prime)
    (signed : LogUpBalanced ledger) : (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  have fits : (Balance.logUp (F := F)).fits ledger.length = true := by
    simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n] using small
  exact ⟨fits,Balance.logUp.balancedInteractions_of_balanced ledger fits signed⟩

/-- For every admitted tape, Clean's actual LogUp count checks pass and each active pull
has a matching push. This covers all three complete internal ledgers of the four demand tables. -/
theorem native_private_matches {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F) :
    ∃ entries, native? image source events readers = some entries ∧
      let r := inputs entries
      ∃ hc hn hs hw,
        let call := openTable r.openings data hc
        let node := stepTable r.nodes data hn
        let seed := Words.seedTable r.contents data hs
        let body := Words.wordTable r.words data hw
        ∀ ledger ∈ [call.interactionsWith WriteAllocation.cursorChannel.toRaw ++ node.interactionsWith WriteAllocation.cursorChannel.toRaw,
          node.interactionsWith contentsChannel.toRaw ++ seed.interactionsWith contentsChannel.toRaw,
          seed.interactionsWith Words.cursorChannel.toRaw ++ body.interactionsWith Words.cursorChannel.toRaw],
          (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  obtain ⟨entries,built,tables,nodes,seeds,words⟩ := native_allocation_assembly run readers data
  obtain ⟨hc,hn,hs,hw,_,_,_,_,_,_,_,_,call,node,body⟩ := tables
  obtain ⟨cc,cn,cw⟩ := allocation_occurrences (inputs entries) data hc hn hs hw
  obtain ⟨actual,collected,_,_,_,_,opens,_⟩ := native_inputs run readers
  cases Option.some.inj (built.symm.trans collected)
  have eventsFit := run.2.2.1 .events
  rw [run.1.2.resources_events] at eventsFit
  have openings : WitnessGeneration.demandHeight (inputs entries).openings.length ≤ 2^21 :=
    WitnessGeneration.demandHeight_le_pow (opens ▸ (List.countP_le_length ..).trans eventsFit)
  have safe : 2^29 + 2*2^29 < SP1Prime := by decide
  refine ⟨entries,built,hc,hn,hs,hw,?_⟩
  dsimp only
  intro ledger member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact checked_balance _ (by rw [cc]; omega) call
  · exact checked_balance _ (by rw [cn]; omega) node
  · exact checked_balance _ (by rw [cw]; omega) body

end SP1Clean.WriteEffects.Witness
