import SP1Clean.Proofs.Completeness.HintQueueReaders
import SP1Clean.Native.Operations.HintQueueSource
import SP1Clean.Native.Operations.HintQueueWordSource
import SP1Clean.Math.WordEquality
import ToClean.Air.StaticReadCounts

/-! # Funding the fixed part of the immutable queue inventory

The original allocation frontier separates input pointers from pointers created by later WRITEs. A request below
that frontier is reconstructed from the fixed source array, even if it was read after a pop. All uses share
one count on the actual resource provider and every source/padding row remains present.
-/

namespace SP1Clean.TraceGen.HintQueueReaders
open Circuit Air.Flat Semantics HintQueue Machine FormalModel.Shard Soundness.Target
private abbrev F := ZMod SP1Prime

/-- Split by immutable pointer identity, retaining all occurrences within each side. -/
def Demand.select (d : Demand) (keep : Nat → Bool) : Demand :=
  ⟨d.nodes.filter (fun r => keep (Address.toNat r.pointer)),d.words.filter (fun r => keep (Address.toNat r.pointer))⟩

/-- A well-formed bound node is exactly its canonical immutable payload at this pointer. -/
theorem node_canonical {r : NodeRecord F} {store : Store} (valid : r.Valid) (binds : r.Binds store) :
    ∃ node, node? store (Address.toNat r.pointer) = some node ∧ NodeRecord.encode (Address.toNat r.pointer) node = r := by
  obtain ⟨node,found,tail,length⟩ := binds
  refine ⟨node,found,?_⟩
  have size : bitVecToWord (BitVec.ofNat 64 node.bytes.length) = r.length := Word.eq_of_toBitVec64_eq
    (isU64_bitVecToWord _) valid.2.2.2 ((toBitVec64_bitVecToWord _).trans length.symm)
  cases r
  simp only [NodeRecord.encode,← tail,Address.ofNat_toNat valid.1,Address.ofNat_toNat valid.2.1,size]

/-- The pointer and index of a bound word identify its entire stored payload, including the final marker. -/
theorem word_canonical {r : WordRecord F} {store : Store} (valid : r.Valid) (binds : r.Binds store) :
    ∃ node, node? store (Address.toNat r.pointer) = some node ∧ Address.toNat r.index < wordCount node.bytes ∧
      WordRecord.encode (Address.toNat r.pointer) node.bytes (Address.toNat r.index) = r := by
  obtain ⟨node,found,inside,value,last⟩ := binds
  refine ⟨node,found,inside,?_⟩
  have same : bitVecToWord (wordValue node.bytes (Address.toNat r.index)) = r.value :=
    Word.eq_of_toBitVec64_eq (isU64_bitVecToWord _) valid.2.2.2.1 ((toBitVec64_bitVecToWord _).trans value.symm)
  cases r
  simp only [WordRecord.encode,Address.ofNat_toNat valid.1,Address.ofNat_toNat valid.2.2.1,same,← last]

/-- At an incoming pointer the two original fixed tables contain every demanded complete payload. -/
theorem incoming_covered {hints : List Bytes} {store : Store} {d : Demand}
    (ext : Extends (ofList hints).1 store) (valid : d.Binds store)
    (nodes : hints.length ≤ SP1Prime - 1) (bytes : (hints.map List.length).sum ≤ SP1Prime - 1) :
    let ds := d.select (fun ptr => ptr ≤ hints.length)
    (∀ r ∈ ds.nodes, (sourceTable hints).Spec r) ∧ (∀ r ∈ ds.words, (HostHintQueue.sourceWordInventory hints).Spec r) := by
  have bound : hints.length < 2^48 := nodes.trans_lt (by decide)
  constructor
  · intro r used
    obtain ⟨used,inRange⟩ := List.mem_filter.mp used
    have old : Address.toNat r.pointer ≤ (ofList hints).1.size := by simpa only [ofList_size,decide_eq_true_eq] using inRange
    obtain ⟨good,later⟩ := valid.1 r used
    obtain ⟨node,atNode,same⟩ := node_canonical good (later.restrict ext old)
    generalize ptr : Address.toNat r.pointer = i at old atNode same
    cases i with
    | zero => contradiction
    | succ i =>
      have index : i < (ofList hints).1.size := by omega
      have actual : (ofList hints).1[i] = node := Option.some.inj ((Array.getElem?_eq_getElem index).symm.trans atNode)
      rw [← same,← actual]
      exact sourceTable_complete hints bound ⟨i,index⟩
  · intro r used
    obtain ⟨used,inRange⟩ := List.mem_filter.mp used
    have old : Address.toNat r.pointer ≤ (ofList hints).1.size := by simpa only [ofList_size,decide_eq_true_eq] using inRange
    obtain ⟨good,later⟩ := valid.2 r used
    obtain ⟨node,atNode,inside,same⟩ := word_canonical good (later.restrict ext old)
    rw [HostHintQueue.sourceWordInventory_of_limits hints _ nodes bytes (by decide)]
    generalize ptr : Address.toNat r.pointer = i at old atNode same
    cases i with
    | zero => contradiction
    | succ i =>
      have index : i < (ofList hints).1.size := by omega
      have actual : (ofList hints).1[i] = node := Option.some.inj ((Array.getElem?_eq_getElem index).symm.trans atNode)
      have fits := Address.toNat_lt good.2.2.1
      subst node
      have paid := sourceWordTable_complete (p := SP1Prime) hints bound ⟨i,index⟩ (Address.toNat r.index) inside fits
      exact (congrArg (sourceWordTable (p := SP1Prime) hints).Spec same).mp paid

/-- Reader funding on an actual fixed component, with every original physical multiplicity occurrence. -/
structure FixedReads (table : Table F) (component : Component F) {M : TypeMap} [ProvableType M]
    (ch : Channel F M) (height : Nat) (reads : List (M F)) : Prop where
  /-- The table has exactly the installed component identity. -/
  source : table.component = component
  /-- Its original physical constraints hold. -/
  constraints : table.Constraints
  /-- Its published channel records meet the component guarantees. -/
  guarantees : table.Guarantees
  /-- One physical emission site per original preallocated row, including unused rows. -/
  count : (table.interactionsWith ch.toRaw).length = height
  /-- The table's actual signed ledger funds all assigned reads and no others. -/
  signed : LogUpBalanced (table.interactionsWith ch.toRaw ++ reads.map ch.pulledValue)

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)

/-- The canonical outgoing cursor from replaying the immutable store updates on the real tape. -/
noncomputable def finalCursor : Store × ℕ :=
  (storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints)).get (by
    obtain ⟨cursor,done,_⟩ := native_demand run
    exact Option.isSome_iff_exists.mpr ⟨cursor,done⟩)

/-- Concrete replay returns the chosen outgoing cursor. -/
theorem finalCursor_done :
    storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some (finalCursor run) :=
  (Option.some_get _).symm

/-- All and only reader occurrences supplied by the original immutable prefix, in order. -/
noncomputable def incomingDemand : Demand :=
  let cursor := finalCursor run
  (collect (history image source events) (snapshot cursor.1 cursor.2 target.host.io.hints)).select
    (fun ptr => ptr ≤ source.host.io.hints.length)

private theorem incomingDemand_covered :
    (∀ r ∈ (incomingDemand run).nodes, (sourceTable source.host.io.hints).Spec r) ∧
    (∀ r ∈ (incomingDemand run).words, (HostHintQueue.sourceWordInventory source.host.io.hints).Spec r) := by
  obtain ⟨cursor,done,valid,ext⟩ := native_demand run
  cases Option.some.inj (done.symm.trans (finalCursor_done run))
  exact incoming_covered ext valid (run.2.2.2.1 .liveHints) (run.2.2.2.1 .liveHintBytes)

/-- The original node resource with genuine metadata-reader counts in its physical rows. -/
noncomputable def fixedNodes (data : ProverData F) : Table F :=
  let hints := source.host.io.hints
  (sourceTable hints).countedPayload HostHintQueue.nodeChannel (fun r good _ => (sourceTable_sound hints r good).1)
    (HostHintQueue.source_height_lt_uint64 hints) (incomingDemand run).nodes (incomingDemand_covered run).1 data

/-- The original word resource with genuine word-reader counts in its physical rows. -/
noncomputable def fixedWords (data : ProverData F) : Table F :=
  let hints := source.host.io.hints
  (HostHintQueue.sourceWordInventory hints).countedPayload HostHintQueue.wordChannel
    (fun r good _ => (sourceWordTable_sound hints r (HostHintQueue.sourceWordInventory_spec hints r good)).1)
    (HostHintQueue.sourceWord_height_lt_uint64 hints) (incomingDemand run).words (incomingDemand_covered run).2 data

/-- Exact signed fixed metadata ledger and actual registered component identity. -/
theorem fixedNodes_checked (data : ProverData F) :
    FixedReads (fixedNodes run data) (HostHintQueue.source source.host.io.hints) HostHintQueue.nodeChannel
      (sourceTable (p := SP1Prime) source.host.io.hints).height (incomingDemand run).nodes := by
  have good := (sourceTable source.host.io.hints).countedPayload_checked HostHintQueue.nodeChannel
    (fun r h _ => (sourceTable_sound _ r h).1) (HostHintQueue.source_height_lt_uint64 _) _ (incomingDemand_covered run).1 data
  exact ⟨rfl,good.1,good.2.1,good.2.2.1,good.2.2.2⟩

/-- Exact signed fixed word ledger and actual registered component identity. -/
theorem fixedWords_checked (data : ProverData F) :
    FixedReads (fixedWords run data) (HostHintQueue.sourceWord source.host.io.hints) HostHintQueue.wordChannel
      (HostHintQueue.sourceWordInventory (p := SP1Prime) source.host.io.hints).height (incomingDemand run).words := by
  have good := (HostHintQueue.sourceWordInventory source.host.io.hints).countedPayload_checked HostHintQueue.wordChannel
    (fun r h _ => (sourceWordTable_sound _ r (HostHintQueue.sourceWordInventory_spec _ r h)).1)
    (HostHintQueue.sourceWord_height_lt_uint64 _) _ (incomingDemand_covered run).2 data
  exact ⟨rfl,good.1,good.2.1,good.2.2.1,good.2.2.2⟩

/-- Construct both existing fixed queue providers from the genuine combined HINT_LEN, HINT_READ and
snapshot reads. Requests above the incoming frontier remain the responsibility of the subsequent allocations. -/
theorem native_fixed_readers {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    ∃ cursor, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some cursor ∧
      let hints := source.host.io.hints
      let d := collect (history image source events) (snapshot cursor.1 cursor.2 target.host.io.hints)
      let old := d.select (fun ptr => ptr ≤ hints.length)
      ∃ nodeTable wordTable, FixedReads nodeTable (HostHintQueue.source hints) HostHintQueue.nodeChannel (sourceTable (p := SP1Prime) hints).height old.nodes ∧
        FixedReads wordTable (HostHintQueue.sourceWord hints) HostHintQueue.wordChannel (HostHintQueue.sourceWordInventory (p := SP1Prime) hints).height old.words :=
  ⟨finalCursor run,finalCursor_done run,fixedNodes run data,fixedWords run data,
    fixedNodes_checked run data,fixedWords_checked run data⟩

end SP1Clean.TraceGen.HintQueueReaders
