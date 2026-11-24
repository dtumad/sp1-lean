import SP1Clean.Proofs.Completeness.HintQueueFundedAllocations

/-! # Funding immutable queue readers from both installed publisher families

The original source table and the new allocation table share the pointer frontier and the
actual execution's demand. Their signed sum pays for every repeated hint and snapshot read.
The private allocation joins use the same funded word table.
-/

namespace SP1Clean.TraceGen.HintQueueReaders

open Air.Flat Circuit Semantics HintQueue Machine FormalModel.Shard WriteAllocation WriteEffects WriteEffects.Witness

private abbrev F := ZMod SP1Prime

private theorem fund_pointers {M : TypeMap} [ProvableType M] (channel : Channel F M)
    (fixed fresh : List (Interaction F)) (requests : List (M F)) (ptr : M F → Nat) (cut : Nat)
    (sourcePaid : LogUpBalanced (fixed ++ (requests.filter (fun r => decide (ptr r ≤ cut))).map channel.pulledValue))
    (freshPaid : LogUpBalanced (fresh ++ (requests.filter (fun r => decide (cut < ptr r))).map channel.pulledValue)) :
    LogUpBalanced (fixed ++ fresh ++ requests.map channel.pulledValue) := by
  intro msg
  have inventory := (List.filter_append_perm (fun r => decide (ptr r ≤ cut)) requests).map channel.pulledValue
  simp only [List.map_append, ← decide_not, Nat.not_le] at inventory
  rw [balanceOf_append, balanceOf_append, ← balanceOf_perm inventory, balanceOf_append]
  have left := sourcePaid msg
  have right := freshPaid msg
  rw [balanceOf_append] at left right
  linear_combination left + right

/-- Combine the exact signed statements on the two original fixed tables with the two
physical allocation tables sharing the same demand. Any installed realization of those
four tables can use this form directly. -/
theorem joint_signed {entries : List Entry} {before after : HostState} {data : ProverData F}
    {s : SixTables entries before after} {fixedNodes fixedWords : Table F} (q : Demand)
    (fixedNodePaid : FixedReads fixedNodes (HostHintQueue.source before.io.hints) HostHintQueue.nodeChannel
      (sourceTable (p := SP1Prime) before.io.hints).height (q.select (fun ptr => ptr ≤ before.io.hints.length)).nodes)
    (fixedWordPaid : FixedReads fixedWords (HostHintQueue.sourceWord before.io.hints) HostHintQueue.wordChannel
      (HostHintQueue.sourceWordInventory (p := SP1Prime) before.io.hints).height (q.select (fun ptr => ptr ≤ before.io.hints.length)).words)
    (freshPaid : AllocationReads s (q.select (fun ptr => before.io.hints.length < ptr)) data) :
    LogUpBalanced (fixedNodes.interactionsWith HostHintQueue.nodeChannel.toRaw ++
      (s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw ++ q.nodes.map HostHintQueue.nodeChannel.pulledValue) ∧
    LogUpBalanced (fixedWords.interactionsWith HostHintQueue.wordChannel.toRaw ++
      (s.words data).interactionsWith HostHintQueue.wordChannel.toRaw ++ q.words.map HostHintQueue.wordChannel.pulledValue) :=
  ⟨fund_pointers HostHintQueue.nodeChannel _ _ _ (fun r => Address.toNat r.pointer) _ fixedNodePaid.signed freshPaid.nodes,
   fund_pointers HostHintQueue.wordChannel _ _ _ (fun r => Address.toNat r.pointer) _ fixedWordPaid.signed freshPaid.words⟩

/-- Exact physical incidence of the two publisher families. The complete original fixed
inventories emit even when unused, and demand padding retains its own zero-weight sites.
These counts can be combined with the physical reader-table heights for a channel bound. -/
theorem publisher_sites {entries : List Entry} {before after : HostState} {data : ProverData F}
    {s : SixTables entries before after} {fixedNodes fixedWords : Table F} {old new : Demand}
    (nodes : FixedReads fixedNodes (HostHintQueue.source before.io.hints) HostHintQueue.nodeChannel
      (sourceTable (p := SP1Prime) before.io.hints).height old.nodes)
    (words : FixedReads fixedWords (HostHintQueue.sourceWord before.io.hints) HostHintQueue.wordChannel
      (HostHintQueue.sourceWordInventory (p := SP1Prime) before.io.hints).height old.words)
    (allocated : AllocationReads s new data) :
    (fixedNodes.interactionsWith HostHintQueue.nodeChannel.toRaw ++
      (s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw).length =
      (sourceTable (p := SP1Prime) before.io.hints).height + WitnessGeneration.demandHeight (inputs entries).nodes.length ∧
    (fixedWords.interactionsWith HostHintQueue.wordChannel.toRaw ++
      (s.words data).interactionsWith HostHintQueue.wordChannel.toRaw).length =
      (HostHintQueue.sourceWordInventory (p := SP1Prime) before.io.hints).height +
        WitnessGeneration.demandHeight (inputs entries).words.length := by
  rw [List.length_append, List.length_append, nodes.count, words.count, allocated.nodeSites, allocated.wordSites]
  exact ⟨rfl, rfl⟩

/-- Signed immutable node and word channels for a single native execution. Both original fixed
tables and both dynamic publisher tables fund requests on the same chronological query list,
including the outgoing snapshot, at their complete physical heights. -/
theorem native_joint_funding {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    ∃ final, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final ∧
      let q := collect (history image source events) (snapshot final.1 final.2 target.host.io.hints)
      let old := q.select (fun ptr => ptr ≤ source.host.io.hints.length)
      let new := q.select (fun ptr => source.host.io.hints.length < ptr)
      ∃ entries, native? image source events new.readers = some entries ∧
        ∃ (s : SixTables entries source.host target.host) (fixedNodes fixedWords : Table F),
          s.Checked data ∧ AllocationReads s new data ∧
          FixedReads fixedNodes (HostHintQueue.source source.host.io.hints) HostHintQueue.nodeChannel
            (sourceTable (p := SP1Prime) source.host.io.hints).height old.nodes ∧
          FixedReads fixedWords (HostHintQueue.sourceWord source.host.io.hints) HostHintQueue.wordChannel
            (HostHintQueue.sourceWordInventory (p := SP1Prime) source.host.io.hints).height old.words ∧
          LogUpBalanced (fixedNodes.interactionsWith HostHintQueue.nodeChannel.toRaw ++
            (s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw ++ q.nodes.map HostHintQueue.nodeChannel.pulledValue) ∧
          LogUpBalanced (fixedWords.interactionsWith HostHintQueue.wordChannel.toRaw ++
            (s.words data).interactionsWith HostHintQueue.wordChannel.toRaw ++ q.words.map HostHintQueue.wordChannel.pulledValue) := by
  obtain ⟨final, done, entries, populated, tables, checked, freshPaid⟩ := native_funded_allocations run data
  obtain ⟨cursor, found, fixedNodes, fixedWords, nodePaid, wordPaid⟩ := native_fixed_readers run data
  have same : cursor = final := Option.some.inj (found.symm.trans done)
  subst cursor
  exact ⟨final, done, entries, populated, tables, fixedNodes, fixedWords, checked, freshPaid, nodePaid, wordPaid,
    joint_signed _ nodePaid wordPaid freshPaid⟩

end SP1Clean.TraceGen.HintQueueReaders
