import SP1Clean.Proofs.Completeness.WriteNativeBlockBalance
import SP1Clean.Proofs.Completeness.WriteWitnessAllocationCounts

/-! # One physical group, fixed block source, and four allocation tables

The group and endpoint inputs are collected with the allocation batches. The immutable word
walk is then funded once, preserving its internal cursor receipts and independent published
queue words. Both the three private joins and the external block ledger use that same table.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- All data-dependent sizes and block indices used to generate the six native tables from a
single chronological collection. Multiplicities are computed from the assigned occurrences. -/
structure SixTables (entries : List Entry) (source target : HostState) where
  /-- Each private placement contributes one use of a real allocated word. -/
  direct : List (Fin (inputs entries).words.length)
  /-- Public placements read the original preallocated endpoint table. -/
  publicReads : List (Fin (blockTable (p := SP1Prime) (.fromEndpoints source target)).height)
  /-- Returned hook words also read the same endpoint table. -/
  returns : List (Fin (blockTable (p := SP1Prime) (.fromEndpoints source target)).height)
  /-- Group table height in the physical row domain. -/
  groupFit : WitnessGeneration.demandHeight (entries.flatMap (Entry.placementGroups (.fromEndpoints source target))).length ≤ UInt64.size
  /-- Fixed endpoint height in the physical row-index domain. -/
  fixedFit : (blockTable (p := SP1Prime) (.fromEndpoints source target)).height < UInt64.size
  /-- Shared opening table height. -/
  openFit : WitnessGeneration.demandHeight (inputs entries).openings.length ≤ UInt64.size
  /-- Shared node-step table height. -/
  nodeFit : WitnessGeneration.demandHeight (inputs entries).nodes.length ≤ UInt64.size
  /-- Shared contents-seed table height. -/
  seedFit : WitnessGeneration.demandHeight (inputs entries).contents.length ≤ UInt64.size
  /-- Original word count before filling the independent block-reader field. -/
  wordFit : WitnessGeneration.demandHeight (inputs entries).words.length ≤ UInt64.size

variable {entries : List Entry} {source target : HostState}

/-- One chronological group for every guest word on every descriptor route. -/
def SixTables.groups (s : SixTables entries source target) (data : ProverData F) : Table F :=
  groupTable (entries.flatMap (Entry.placementGroups (.fromEndpoints source target))) data s.groupFit

/-- Single fixed provider funded by the public placement and returned-word reads together. -/
def SixTables.fixed (s : SixTables entries source target) (data : ProverData F) : Table F :=
  (blockTable (p := SP1Prime) (.fromEndpoints source target)).buildPayload blockChannel (by intros; trivial)
    s.fixedFit (fun i => ((ReaderCounts.counts (s.publicReads ++ s.returns))[i] : F)) data

/-- Shared chronological allocation openings. -/
def SixTables.calls (s : SixTables entries source target) (data : ProverData F) : Table F :=
  openTable (inputs entries).openings data s.openFit

/-- Shared allocation steps at permanent node pointers. -/
def SixTables.nodes (s : SixTables entries source target) (data : ProverData F) : Table F :=
  stepTable (inputs entries).nodes data s.nodeFit

/-- One original contents seed per permanent node. -/
def SixTables.seeds (s : SixTables entries source target) (data : ProverData F) : Table F :=
  Words.seedTable (inputs entries).contents data s.seedFit

/-- The sole funded word table used by both cursor and block joins. -/
def SixTables.words (s : SixTables entries source target) (data : ProverData F) : Table F :=
  Words.wordTable (fundedWords (inputs entries).words s.direct) data (by rw [fundedWords_length]; exact s.wordFit)

/-- The original physical ledgers for the three private allocation channels. -/
noncomputable def SixTables.privateLedgers (s : SixTables entries source target) (data : ProverData F) : List (List (Interaction F)) :=
  [(s.calls data).interactionsWith WriteAllocation.cursorChannel.toRaw ++ (s.nodes data).interactionsWith WriteAllocation.cursorChannel.toRaw,
   (s.nodes data).interactionsWith contentsChannel.toRaw ++ (s.seeds data).interactionsWith contentsChannel.toRaw,
   (s.seeds data).interactionsWith Words.cursorChannel.toRaw ++ (s.words data).interactionsWith Words.cursorChannel.toRaw]

/-- All four external sites use the original block channel and this same funded word table. -/
noncomputable def SixTables.blockLedger (s : SixTables entries source target) (data : ProverData F) : List (Interaction F) :=
  (s.groups data).interactionsWith blockChannel.toRaw ++ (s.words data).interactionsWith blockChannel.toRaw ++
    (s.fixed data).interactionsWith blockChannel.toRaw

/-- Validation of the original six components, their private joins, and their signed block
ledger. At full native limits, the external count needs its separate sharp physical test. -/
structure SixTables.Checked (s : SixTables entries source target) (data : ProverData F) : Prop where
  /-- Original identities, constraints, guarantees, signed block balance and exact block count. -/
  blocks : CombinedBlocksChecked source target (entries.flatMap (Entry.placementGroups (.fromEndpoints source target))).length
    (inputs entries).words.length (s.groups data) (s.words data) (s.fixed data)
  /-- Mandatory opening for every direct hint or hook, including zero-buffer replies. -/
  calls : (s.calls data).component = openComponent ∧ (s.calls data).Constraints ∧ (s.calls data).Guarantees
  /-- Actual node allocation steps in the persistent store. -/
  nodes : (s.nodes data).component = stepComponent ∧ (s.nodes data).Constraints ∧ (s.nodes data).Guarantees
  /-- Actual contents seeds at those same pointers. -/
  seeds : (s.seeds data).component = Words.seedComponent ∧ (s.seeds data).Constraints ∧ (s.seeds data).Guarantees
  /-- All three private joins meet signed, physical count, and message-matching checks. -/
  privateMatches : ∀ ledger ∈ s.privateLedgers data, LogUpBalanced ledger ∧
    (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger
  /-- Funding leaves the immutable word and its independent queue-reader count in place. -/
  queueWords : (fundedWords (inputs entries).words s.direct).map (fun r => (r.wordReads,r.word)) =
    (inputs entries).words.map (fun r => (r.wordReads,r.word))

/-- The native constructor funds one word table for all four joins. Collection uniqueness
identifies the openings, nodes, seeds and words used by both physical component arguments.
Initial block multiplicities need no external input. -/
theorem native_six_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)
    (nodeReads : HintQueue.NodeRecord F → F) (wordReads : HintQueue.WordRecord F → F) :
    let readers : Readers := ⟨nodeReads,fun _ => 0,wordReads⟩
    ∃ entries, native? image source events readers = some entries ∧
      ∃ s : SixTables entries source.host target.host, s.Checked data := by
  intro readers
  obtain ⟨entries,collected,direct,publicReads,returns,hg,_,hf,block⟩ := native_block_tables run data nodeReads wordReads
  obtain ⟨other,replayed,installed,_⟩ := native_allocation_assembly run readers data
  cases Option.some.inj (collected.symm.trans replayed)
  obtain ⟨hc,hn,hs,hw,callOK,callG,nodeOK,nodeG,seedOK,seedG,_,_,call,node,body⟩ := installed
  obtain ⟨other,replayed,_,_,_,_,matching⟩ := native_private_matches run readers data
  cases Option.some.inj (collected.symm.trans replayed)
  let s : SixTables entries source.host target.host := ⟨direct,publicReads,returns,hg,hf,hc,hn,hs,hw⟩
  refine ⟨entries,collected,s,block,⟨rfl,callOK,callG⟩,⟨rfl,nodeOK,nodeG⟩,⟨rfl,seedOK,seedG⟩,?_,fundedWords_queue ..⟩
  intro ledger member
  have same := fundedWords_cursors (inputs entries).words direct data hw
  change ledger ∈ [_,_,(s.seeds data).interactionsWith Words.cursorChannel.toRaw ++
    (Words.wordTable (fundedWords (inputs entries).words direct) data _).interactionsWith Words.cursorChannel.toRaw] at member
  rw [same] at member
  refine ⟨?_,matching ledger member⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact call
  · exact node
  · exact body

end SP1Clean.WriteEffects.Witness
