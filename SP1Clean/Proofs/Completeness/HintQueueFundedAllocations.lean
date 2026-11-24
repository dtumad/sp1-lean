import SP1Clean.Proofs.Completeness.HintQueueFreshCoverage
import SP1Clean.Proofs.Completeness.HintQueueAllocationLedgers
import SP1Clean.Proofs.Completeness.WriteAllocationSix
import ToClean.Air.PayloadReadCounts

/-! # Funding every newly allocated permanent node and padded word

Actual syscall and outgoing snapshot demands determine the dynamic publication counts. Clean's native demand tally
counts the shared typed requests once. The funded allocation word table also participates in the private cursors and
the external WRITE block ledger, using the original independent block-read column.
-/

namespace SP1Clean.TraceGen.HintQueueReaders
open Air.Flat Circuit Semantics HintQueue Machine FormalModel.Shard WriteAllocation WriteEffects WriteEffects.Witness
private abbrev F := ZMod SP1Prime

/-- Use Clean's one-pass payload tallies to supply the two queue counts of each fresh allocation.
Block reads are assigned independently by the shared block constructor. -/
def Demand.readers (q : Demand) : Readers :=
  let nodeUses := ReaderCounts.byPayload HostHintQueue.nodeChannel q.nodes
  let wordUses := ReaderCounts.byPayload HostHintQueue.wordChannel q.words
  ⟨fun n => (nodeUses n : F),fun _ => 0,fun w => (wordUses w : F)⟩

private theorem projections {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (emitted : native? image source events readers = some entries) {final : Store × Nat}
    (done : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final) :
    let published := fresh final.1 (ofList source.host.io.hints).1.size
    (inputs entries).nodes.map (fun r => (r.readers,r.node.node)) =
      published.nodes.map (fun n => (readers.nodes n,n)) ∧
    (inputs entries).words.map (fun r => (r.wordReads,r.word)) =
      published.words.map (fun w => (readers.words w,w)) := by
  have same := native_publication_range run readers emitted done
  constructor
  · have nodes := congrArg (List.map Publication.node) same
    simp only [inputs,List.map_map,Function.comp_def,fresh,nodeAt,storedPublication,publication] at nodes ⊢
    exact nodes
  · have words := congrArg (List.flatMap Publication.words) same
    simp only [inputs,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,storedPublication,publication,fresh,wordsAt] at words ⊢
    simpa only [List.map_ofFn,Function.comp_def] using words

/-- These are the same fresh node/word components returned by six-table block funding, at the same caller-independent counts. -/
structure AllocationReads {entries : List Entry} {before after : HostState} (s : SixTables entries before after)
    (reads : Demand) (data : ProverData F) : Prop where
  /-- All occupied and padded node rows have their original emission site. -/
  nodeSites : ((s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw).length = WitnessGeneration.demandHeight (inputs entries).nodes.length
  /-- All occupied and padded word rows have their independent immutable-word site. -/
  wordSites : ((s.words data).interactionsWith HostHintQueue.wordChannel.toRaw).length = WitnessGeneration.demandHeight (inputs entries).words.length
  /-- The original dynamic node table funds exactly the node requests above the incoming frontier. -/
  nodes : LogUpBalanced ((s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw ++ reads.nodes.map HostHintQueue.nodeChannel.pulledValue)
  /-- The same funded word table pays for all fresh immutable-word consumers. -/
  words : LogUpBalanced ((s.words data).interactionsWith HostHintQueue.wordChannel.toRaw ++ reads.words.map HostHintQueue.wordChannel.pulledValue)

private theorem lookup_funding {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {final : Store × Nat}
    (done : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final)
    (d : Demand) (auth : d.Binds final.1) (data : ProverData F)
    {entries : List Entry} {s : SixTables entries source.host target.host}
    (emitted : native? image source events (d.select (fun ptr => source.host.io.hints.length < ptr)).readers = some entries) :
    AllocationReads s (d.select (fun ptr => source.host.io.hints.length < ptr)) data := by
  let uses := d.select (fun ptr => source.host.io.hints.length < ptr)
  let supplies := fresh final.1 source.host.io.hints.length
  obtain ⟨width,sizes⟩ := native_store_sizes run done
  obtain ⟨distinctN,distinctW⟩ := fresh_unique final.1 source.host.io.hints.length width sizes
  obtain ⟨containsN,containsW⟩ := fresh_covered source.host.io.hints.length auth
  have nodePaid := ReaderCounts.unique_balanced HostHintQueue.nodeChannel supplies.nodes uses.nodes distinctN containsN
  have wordPaid := ReaderCounts.unique_balanced HostHintQueue.wordChannel supplies.words uses.words distinctW containsW
  obtain ⟨nodes,words⟩ := projections run uses.readers emitted done
  rw [ofList_size] at nodes words
  let n := (inputs entries).nodes
  let w := fundedWords (inputs entries).words s.direct
  have ws : w.map (fun r => (r.wordReads,r.word)) = supplies.words.map (fun v => (uses.readers.words v,v)) :=
    (fundedWords_queue ..).trans words
  have nEmit := congrArg (List.map (fun (count,record) => HostHintQueue.nodeChannel.emittedValue count record)) nodes
  have wEmit := congrArg (List.map (fun (count,record) => HostHintQueue.wordChannel.emittedValue count record)) ws
  simp only [List.map_map,Function.comp_def] at nEmit wEmit
  have rawN := stepTable_nodes n data s.nodeFit
  have rawW := wordTable_queueWords w data (show WitnessGeneration.demandHeight w.length ≤ UInt64.size by
    rw [fundedWords_length]; exact s.wordFit)
  change (s.nodes data).interactionsWith HostHintQueue.nodeChannel.toRaw = _ at rawN
  change (s.words data).interactionsWith HostHintQueue.wordChannel.toRaw = _ at rawW
  constructor
  · rw [rawN,List.length_map,WitnessGeneration.guardedRows_length]
  · rw [rawW,List.length_map,WitnessGeneration.guardedRows_length,fundedWords_length]
  · intro msg
    rw [rawN,balanceOf_append,WitnessGeneration.guarded_emit_sum HostHintQueue.nodeChannel n (fun r => r.readers) (fun r => r.node.node),nEmit]
    exact (balanceOf_append ..).symm.trans (nodePaid msg)
  · intro msg
    rw [rawW,balanceOf_append,WitnessGeneration.guarded_emit_sum HostHintQueue.wordChannel w (fun r => r.wordReads) (fun r => r.word),wEmit]
    exact (balanceOf_append ..).symm.trans (wordPaid msg)

/-- Requests above the immutable incoming frontier on the same replay used by both fixed providers. -/
noncomputable def freshDemand {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) : Demand :=
  let cursor := finalCursor run
  (collect (history image source events) (snapshot cursor.1 cursor.2 target.host.io.hints)).select
    (fun ptr => source.host.io.hints.length < ptr)

/-- Any six-table construction on the actual fresh demand has its immutable publication
columns funded by precisely the corresponding readers, independently of its block funding. -/
theorem freshDemand_funded {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)
    {entries : List Entry} (emitted : native? image source events (freshDemand run).readers = some entries)
    (s : SixTables entries source.host target.host) : AllocationReads s (freshDemand run) data := by
  obtain ⟨cursor,done,auth,_⟩ := native_demand run
  cases Option.some.inj (done.symm.trans (finalCursor_done run))
  exact lookup_funding run (finalCursor_done run) _ auth data emitted

/-- A native execution generates all six allocation/placement tables on the same collection, with both immutable
reader columns derived from the actual demands. The independent block, contents and cursor proofs remain on these tables. -/
theorem native_funded_allocations {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    ∃ final, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final ∧
      let d := collect (history image source events) (snapshot final.1 final.2 target.host.io.hints)
      let uses := d.select (fun ptr => source.host.io.hints.length < ptr)
      ∃ entries, native? image source events uses.readers = some entries ∧
        ∃ s : SixTables entries source.host target.host, s.Checked data ∧ AllocationReads s uses data := by
  obtain ⟨final,done,auth,_⟩ := native_demand run
  let d := collect (history image source events) (snapshot final.1 final.2 target.host.io.hints)
  let uses := d.select (fun ptr => source.host.io.hints.length < ptr)
  obtain ⟨entries,emitted,tables,verified⟩ := native_six_tables run data uses.readers.nodes uses.readers.words
  exact ⟨final,done,entries,emitted,tables,verified,lookup_funding run done d auth data emitted⟩

end SP1Clean.TraceGen.HintQueueReaders
