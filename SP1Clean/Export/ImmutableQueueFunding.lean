import SP1Clean.Export.HintSnapshotCapacity
import SP1Clean.Proofs.Completeness.HintHandlerTransfers
import SP1Clean.Proofs.Completeness.HintSnapshotRecords
import SP1Clean.Proofs.Completeness.HintQueueJointFunding

/-! # Joint native funding of the immutable queue node and word ledgers

The five original host readers, two incoming fixed publishers, final snapshot reader, and
two dynamic allocation publishers are traversed in physical slot order. All ten tables use
the same admitted tape, outgoing pointer and immutable reader counts. Declaration of a raw
assembly witness also requires the other installed tables and channels.
-/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen HintQueue HostHintQueue
open WriteEffects.Witness WitnessGeneration

private abbrev F := ZMod SP1Prime

/-- The complete raw ledger, its physical count check, and the resulting Clean interaction conditions. -/
structure FundedImmutableLedger (ledger : List (Interaction F)) (sites : Nat) : Prop where
  /-- Number of physical sites including zero counts and demand padding. -/
  count : ledger.length = sites
  /-- Per-message field balance at the actual publisher multiplicities. -/
  signed : LogUpBalanced ledger
  /-- The physical count fits at the native field characteristic. -/
  fit : (Balance.logUp (F := F)).fits ledger.length = true
  /-- Clean's matched interaction conditions obtained from that checked field sum. -/
  matched : BalancedInteractions ledger

private theorem funded {ledger : List (Interaction F)} {sites : Nat} (count : ledger.length = sites)
    (small : sites < SP1Prime) (signed : LogUpBalanced ledger) : FundedImmutableLedger ledger sites := by
  have fits : (Balance.logUp (F := F)).fits ledger.length = true := by
    simpa only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, count] using small
  exact ⟨count, signed, fits, Balance.logUp.balancedInteractions_of_balanced _ fits signed⟩

private theorem outside (t : Table F) (ch : RawChannel F) (h : ch.name ∉ t.component.circuit.channels.map RawChannel.name) :
    t.interactionsWith ch = [] :=
  t.interactionsWith_nil_of_channel_not_mem fun used => h (List.mem_map_of_mem used)

private theorem assemble {M : TypeMap} [ProvableType M] (ch : Channel F M) (heads fixed ending fresh : List (Interaction F))
    (calls snapshot : List (M F)) (paid : LogUpBalanced (fixed ++ fresh ++ (calls ++ snapshot).map ch.pulledValue))
    (reads : ∀ msg, balanceOf heads msg = balanceOf (calls.map ch.pulledValue) msg)
    (last : ∀ msg, balanceOf ending msg = balanceOf (snapshot.map ch.pulledValue) msg) :
    LogUpBalanced (heads ++ (fixed ++ (ending ++ fresh))) := by
  intro msg
  have closed := paid msg
  rw [List.map_append] at closed
  simp only [balanceOf_append] at closed ⊢
  rw [reads, last]
  linear_combination closed

/-- Both immutable channels are funded and below the field characteristic over all ten
original physical contributors for any mixed execution admitted by the broad native preset.
Both fixed tables satisfy their original contracts. The allocation word table is the one
whose private and block channels are checked in the same six-table construction. -/
theorem native_immutable_queue {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    ∃ final, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final ∧
      let history := HintQueueReaders.history image source events
      let ending := HintQueueReaders.snapshot final.1 final.2 target.host.io.hints
      let demand := HintQueueReaders.collect history ending
      ∃ entries, native? image source events (demand.select (fun ptr => source.host.io.hints.length < ptr)).readers = some entries ∧
        ∃ (s : SixTables entries source.host target.host) (fixedNodes fixedWords : Table F),
          let snap := HostHintSnapshot.tableFor final.1 final.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
          let ts := HintHandlers.readerTables run data ++ [fixedNodes, fixedWords, snap, s.nodes data, s.words data]
          s.Checked data ∧ fixedNodes.component = HostHintQueue.source source.host.io.hints ∧
          fixedWords.component = sourceWord source.host.io.hints ∧ (∀ t ∈ ts, t.Constraints ∧ t.Guarantees) ∧
          FundedImmutableLedger (ts.flatMap (·.interactionsWith nodeChannel.toRaw))
            ((HintHandlers.readTable run data).length + (HintHandlers.lengthTable run false data).length +
             (sourceTable (p := SP1Prime) source.host.io.hints).height + (HostHintSnapshot.inventory (p := SP1Prime) target.host.io.hints).height +
             demandHeight (inputs entries).nodes.length) ∧
          FundedImmutableLedger (ts.flatMap (·.interactionsWith wordChannel.toRaw))
            ((HintHandlers.readTable run data).length + (HintHandlers.transferTable run false data).length +
             (HintHandlers.transferTable run true data).length + (sourceWordInventory (p := SP1Prime) source.host.io.hints).height +
             (HostHintSnapshot.inventory (p := SP1Prime) target.host.io.hints).height + demandHeight (inputs entries).words.length) := by
  obtain ⟨final, finished, entries, collected, s, fnodes, fwords, valid, fresh, nodePaid, wordPaid, nodes, words⟩ :=
    HintQueueReaders.native_joint_funding run data
  let ending := HintQueueReaders.snapshot final.1 final.2 target.host.io.hints
  let history := HintQueueReaders.history image source events
  let snap := HostHintSnapshot.tableFor final.1 final.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
  let hs := HintHandlers.readerTables run data
  have fnSilent : fnodes.interactionsWith wordChannel.toRaw = [] := by
    apply outside
    rw [nodePaid.source]
    exact of_decide_eq_true rfl
  have fwSilent : fwords.interactionsWith nodeChannel.toRaw = [] := by
    apply outside
    rw [wordPaid.source]
    exact of_decide_eq_true rfl
  have dnSilent : (s.nodes data).interactionsWith wordChannel.toRaw = [] := by
    apply outside
    rw [valid.nodes.1]
    exact of_decide_eq_true rfl
  have dwSilent : (s.words data).interactionsWith nodeChannel.toRaw = [] := by
    apply outside
    rw [valid.blocks.wordsValid.1]
    exact of_decide_eq_true rfl
  obtain ⟨other, _, done, _, snapshotWalk⟩ := admissibleExecution_hintSnapshot run
  cases Option.some.inj (done.symm.trans finished)
  have snapOK := HostHintSnapshot.tableFor_valid snapshotWalk (admissible_hint_snapshot_fits run) data
  have snapSums := HostHintSnapshot.tableFor_demands final.1 final.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
  obtain ⟨snapNodes, snapWords⟩ := HostHintSnapshot.tableFor_record_counts final.1 final.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
  obtain ⟨headC, headG, lenOK, transferOK⟩ := HintHandlers.tables_checked run data
  obtain ⟨nodeCount, wordCount, _⟩ := HintHandlers.reader_counts run data
  obtain ⟨_, headBound, lengthHeight, transferHeight⟩ := HintHandlers.tables_heights run data
  have lenBound := (lengthHeight false).2
  have contBound := (transferHeight false).2
  have lastBound := (transferHeight true).2
  obtain ⟨_, _, _, fixedN, fixedW, maxFixed, _⟩ := run.fixed_hint_capacity (by rfl)
  have snapBound := native_hint_snapshot_height run
  have wordMax := native_word_capacity run _ collected
  have wordBound := demandHeight_le_pow wordMax
  have nodeBound := demandHeight_le_pow ((native_node_count run _ collected).trans wordMax)
  have safety : 2^16 + 4*2^28 + 2^29 < SP1Prime := by decide
  refine ⟨final, finished, entries, collected, s, fnodes, fwords, valid, nodePaid.source, wordPaid.source, ?_, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_append, HintHandlers.readerTables, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨headC, headG⟩
    · exact lenOK false
    · exact lenOK true
    · exact transferOK false
    · exact transferOK true
    · exact ⟨nodePaid.constraints, nodePaid.guarantees⟩
    · exact ⟨wordPaid.constraints, wordPaid.guarantees⟩
    · exact snapOK
    · exact valid.nodes.2
    · exact valid.blocks.wordsValid.2
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, fwSilent, dwSilent, List.nil_append]
    apply funded
    · simp only [List.length_append, nodeCount, nodePaid.count, snapNodes, fresh.nodeSites]
      omega
    · omega
    · exact assemble nodeChannel _ _ _ _ (history.flatMap HintQueueReaders.Demand.nodes) ending.nodes nodes
        (fun msg => (HintHandlers.reader_sums run data msg).1) (fun msg => (snapSums msg).1)
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, fnSilent, dnSilent, List.nil_append]
    apply funded
    · simp only [List.length_append, wordCount, wordPaid.count, snapWords, fresh.wordSites]
      omega
    · omega
    · exact assemble wordChannel _ _ _ _ (history.flatMap HintQueueReaders.Demand.words) ending.words words
        (fun msg => (HintHandlers.reader_sums run data msg).2) (fun msg => (snapSums msg).2)

end SP1Clean.Export.InstalledAssembly
