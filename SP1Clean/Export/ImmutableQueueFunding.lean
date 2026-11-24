import SP1Clean.Export.CheckedLedger
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

private theorem funded {ledger : List (Interaction F)} {sites : Nat} (count : ledger.length = sites)
    (small : sites < SP1Prime) (signed : LogUpBalanced ledger) : CheckedLedger ledger sites := by
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

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)

/-- Physical readers and publishers in original registry order, followed by the final snapshot
and the node and word tables from the same WRITE allocation. -/
noncomputable def immutableTables {entries : List Entry} (s : SixTables entries source.host target.host) : List (Table F) :=
  let final := HintQueueReaders.finalCursor run
  let snap := HostHintSnapshot.tableFor final.1 final.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
  HintHandlers.readerTables run data ++ [HintQueueReaders.fixedNodes run data, HintQueueReaders.fixedWords run data,
    snap, s.nodes data, s.words data]

/-- Every padded HINT_READ and nonempty HINT_LEN row, fixed input node, snapshot row and allocation row. -/
noncomputable def immutableNodeSites (entries : List Entry) : Nat :=
  (HintHandlers.readTable run data).length + (HintHandlers.lengthTable run false data).length +
    (sourceTable (p := SP1Prime) source.host.io.hints).height +
    (HostHintSnapshot.inventory (p := SP1Prime) target.host.io.hints).height + demandHeight (inputs entries).nodes.length

/-- Every padded HINT_READ header and transfer, fixed input word, snapshot row and allocation word. -/
noncomputable def immutableWordSites (entries : List Entry) : Nat :=
  (HintHandlers.readTable run data).length + (HintHandlers.transferTable run false data).length +
    (HintHandlers.transferTable run true data).length + (sourceWordInventory (p := SP1Prime) source.host.io.hints).height +
    (HostHintSnapshot.inventory (p := SP1Prime) target.host.io.hints).height + demandHeight (inputs entries).words.length

/-- The actual immutable readers and publishers of any checked six-table installation on this
execution fund both complete channels, including the outgoing snapshot and all zero counts. -/
theorem native_immutable_queue {entries : List Entry}
    (collected : native? image source events (HintQueueReaders.freshDemand run).readers = some entries)
    (s : SixTables entries source.host target.host) (valid : s.Checked data) :
    let ts := immutableTables run data s
    (∀ t ∈ ts, t.Constraints ∧ t.Guarantees) ∧
    CheckedLedger (ts.flatMap (·.interactionsWith nodeChannel.toRaw)) (immutableNodeSites run data entries) ∧
    CheckedLedger (ts.flatMap (·.interactionsWith wordChannel.toRaw)) (immutableWordSites run data entries) := by
  let final := HintQueueReaders.finalCursor run
  have finished := HintQueueReaders.finalCursor_done run
  let fnodes := HintQueueReaders.fixedNodes run data
  let fwords := HintQueueReaders.fixedWords run data
  have nodePaid := HintQueueReaders.fixedNodes_checked run data
  have wordPaid := HintQueueReaders.fixedWords_checked run data
  have fresh := HintQueueReaders.freshDemand_funded run data collected s
  obtain ⟨nodes, words⟩ := HintQueueReaders.joint_signed
    (HintQueueReaders.collect (HintQueueReaders.history image source events) (HintQueueReaders.snapshot final.1 final.2 target.host.io.hints))
    nodePaid wordPaid fresh
  let ending := HintQueueReaders.snapshot final.1 final.2 target.host.io.hints
  let history := HintQueueReaders.history image source events
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
  have same := Option.some.inj (done.symm.trans finished)
  subst other
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
  dsimp only [immutableTables, immutableNodeSites, immutableWordSites]
  dsimp only [fnodes] at fnSilent
  dsimp only [fwords] at fwSilent
  dsimp only [final] at snapNodes snapWords
  refine ⟨?_, ?_, ?_⟩
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
