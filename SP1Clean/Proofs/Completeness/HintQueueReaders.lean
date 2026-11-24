import SP1Clean.Proofs.Completeness.HintReadTables
import SP1Clean.Proofs.Completeness.HintSnapshotTables
import SP1Clean.Proofs.Completeness.HintQueueSnapshot
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate

/-! # Immutable queue readers throughout one admitted execution

Empty HINT_LEN reads no metadata, positive HINT_LEN reads the live head, and HINT_READ reads the head
and its terminal padded word, followed by every transfer word before popping it. The outgoing walk adds one metadata use and all padded words
of every surviving node. Queries retain both their full typed payload and their occurrence order.
-/

namespace SP1Clean.TraceGen.HintQueueReaders
open Semantics HintQueue Machine FormalModel.Shard Soundness.Target
private abbrev F := ZMod SP1Prime

/-- Node metadata and aligned hint-word requests, including repeats. -/
structure Demand where
  /-- Nonempty head observations and outgoing snapshot nodes. -/
  nodes : List (NodeRecord F)
  /-- Every observed padded word, including the extra terminal word of an aligned or empty node. -/
  words : List (WordRecord F)

/-- Every demanded field word is canonical and remains readable in the common immutable store. -/
def Demand.Binds (q : Demand) (store : Store) : Prop :=
  (∀ r ∈ q.nodes, r.Valid ∧ r.Binds store) ∧ (∀ r ∈ q.words, r.Valid ∧ r.Binds store)

private def one (pointer : Nat) (node : Node) (words : Bool) : Demand :=
  ⟨[NodeRecord.encode pointer node],if words then
    WordRecord.encode pointer node.bytes (node.bytes.length / 8) :: (List.range (wordCount node.bytes)).map (WordRecord.encode pointer node.bytes) else []⟩

/-- Immutable input messages at one genuine tape cut, using the actual persistent head before the call. -/
def atCursor (cursor : Store × Nat) : ExecutionEvent → Demand
  | .ordinary => ⟨[],[]⟩
  | .syscall call =>
    if call.rawCode = SyscallKind.hintLength.code ∨ call.rawCode = SyscallKind.hintRead.code then
      ((node? cursor.1 cursor.2).map (fun node => one cursor.2 node (decide (call.rawCode = SyscallKind.hintRead.code)))).getD ⟨[],[]⟩
    else ⟨[],[]⟩

/-- The empty length arm has no immutable-node occurrence; the nonempty arm pulls precisely its populated node. -/
theorem length_demand (cursor : Store × Nat) (call : CoreSyscallEvent) (code : call.rawCode = SyscallKind.hintLength.code)
    (prev : Nat) (executed : HostExecution) {hints : List Bytes} (rep : Represents cursor.1 cursor.2 hints) :
    let handler := HostHintLengthChip.populate (p := SP1Prime) cursor.1 cursor.2 prev call.clock executed
    (atCursor cursor (.syscall call)).nodes = (if cursor.2 = 0 then [] else [handler.node]) ∧
    (atCursor cursor (.syscall call)).words = [] := by
  rcases cursor with ⟨store,head⟩
  cases rep with
  | nil => simp [atCursor,code,node?]
  | cons found down _ =>
    have ne := Nat.ne_of_gt (node?_bound found).1
    simp [atCursor,code,found,ne,HostHintLengthChip.populate,one,SyscallKind.code]

/-- A read handler and its last transfer independently pull the same final word. This holds even when
the requested buffer has no data bytes; every transfer retains the original published pointer and index. -/
theorem read_demand (cursor : Store × Nat) (call : CoreSyscallEvent) (code : call.rawCode = SyscallKind.hintRead.code)
    (prev : Nat) (executed : HostExecution) {node : Node} (found : node? cursor.1 cursor.2 = some node)
    (frontier : AccessFrontier) (sail : SailState) :
    let handler := HostHintReadChip.populate (p := SP1Prime) cursor.1 cursor.2 prev call.clock executed
    let request : HintReadTransfers.Request := ⟨call.clock,cursor.2,call.arg1.toNat,node.bytes⟩
    (atCursor cursor (.syscall call)).nodes = [handler.node] ∧
    (atCursor cursor (.syscall call)).words = handler.endStep.word ::
      (request.rows frontier sail).map (fun e => (e.2.1.step e.1).word) := by
  dsimp only
  simp only [atCursor,code,eq_self,or_true,ite_true,decide_true,found,Option.map_some,Option.getD_some,one,
    HostHintReadChip.populate,HostHintReadChip.Inputs.endStep,HintReadTransfers.Request.rows,List.map_map]
  constructor
  · trivial
  congr 1
  · simp [NodeRecord.encode,WordRecord.encode,wordCount]
  · apply List.map_congr_left
    intro i _
    simp [HintReadTransfers.Request.wordRow,HintReadTransfers.Request.last,HintReadWordChip.populate,HintReadWordChip.Inputs.step,
      HostRamAccessChip.populate,WordRecord.encode]

/-- Look up the current queue after exactly the given prefix of mixed execution. -/
noncomputable def at? (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) (i : Nat) : Option Demand := do
  let e ← events[i]?
  let cursor ← storeAfter? (policy SP1Prime image) image.program source.realize (events.take i) (ofList source.host.io.hints)
  pure (atCursor cursor e)

/-- Replay every original guest cut in order when counting readers. -/
noncomputable def history (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent) : List Demand :=
  (List.finRange events.length).filterMap (fun i => at? image source events i.val)

/-- Concatenate the chronological calls and the endpoint without deduplicating payloads. -/
def collect (events : List Demand) (outgoing : Demand) : Demand :=
  ⟨events.flatMap Demand.nodes ++ outgoing.nodes, events.flatMap Demand.words ++ outgoing.words⟩

private theorem empty_binds (store : Store) : (Demand.mk [] []).Binds store := by simp [Demand.Binds]

private theorem atCursor_binds {cursor : Store × Nat} {final : Store} (e : ExecutionEvent)
    (available : HintRecordsAt cursor.1 final) : (atCursor cursor e).Binds final := by
  cases e with
  | ordinary => exact empty_binds _
  | syscall call =>
    simp only [atCursor]
    split
    · cases found : node? cursor.1 cursor.2 with
      | none => exact empty_binds _
      | some node =>
        obtain ⟨valid,binds,_,each⟩ := available _ _ found
        refine ⟨?_,?_⟩
        · intro r mem
          exact (List.mem_singleton.mp mem) ▸ ⟨valid,binds⟩
        intro r mem
        change r ∈ (if decide (call.rawCode = SyscallKind.hintRead.code) then _ else []) at mem
        split at mem
        · rcases List.mem_cons.mp mem with rfl | included
          · exact (each (node.bytes.length / 8) (by simp [wordCount])).2
          obtain ⟨i,inside,rfl⟩ := List.mem_map.mp included
          exact (each i (List.mem_range.mp inside)).2
        · contradiction
    · exact empty_binds _

/-- No original cut is lost by the optional collector. All event reads bind the one final store,
including reads of nodes popped before the outgoing snapshot. -/
theorem history_binds {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {final : Store × Nat}
    (completed : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final) :
    (history image source events).length = events.length ∧ ∀ q ∈ history image source events, q.Binds final.1 := by
  have each (i : Fin events.length) : ∃ q, at? image source events i.val = some q ∧ q.Binds final.1 := by
    obtain ⟨_,cursor,after,_,found,_,_,_,_,_,finish,_,_,records⟩ := admissibleExecution_hintInventory run i
    cases Option.some.inj (completed.symm.trans finish)
    exact ⟨atCursor cursor events[i],by simp [at?,found],atCursor_binds _ records⟩
  constructor
  · unfold history
    rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]
    have live : (List.finRange events.length).filter (fun i => (at? image source events i.val).isSome) = List.finRange events.length := by
      apply List.filter_eq_self.mpr
      intro i _
      obtain ⟨q,found,_⟩ := each i
      simp only [found,Option.isSome_some]
    rw [live,List.length_finRange]
  intro q m
  obtain ⟨i,_,got⟩ := List.mem_filterMap.mp m
  obtain ⟨actual,found,verified⟩ := each i
  exact Option.some.inj (found.symm.trans got) ▸ verified

/-- The outgoing walk consumes the exact records selected by its occupied fixed shapes. -/
def snapshot (store : Store) (head : Nat) (hints : List Bytes) : Demand :=
  let rows := HostHintSnapshot.liveInputs (p := SP1Prime) store 0 head hints
  ⟨rows.filterMap (fun r => if r.1.first = 1 then some (r.1.node r.2.1) else none), rows.map (fun r => r.1.word r.2.1)⟩

private theorem live_binds {store : Store} {head : Nat} {hints : List Bytes} {tails : List Nat}
    (walk : ReadsSnapshot SP1Prime store head hints tails) (start : Nat) :
    ∀ r ∈ HostHintSnapshot.liveInputs (p := SP1Prime) store start head hints,
      (r.1.first = 1 → (r.1.node r.2.1).Valid ∧ (r.1.node r.2.1).Binds store) ∧
      (r.1.word r.2.1).Valid ∧ (r.1.word r.2.1).Binds store := by
  induction hints generalizing start head tails with
  | nil => simp [HostHintSnapshot.liveInputs]
  | cons bytes rest ih =>
    cases tails with
    | nil => contradiction
    | cons tail later =>
      obtain ⟨bound,down,indices,read,suffix⟩ := walk
      have found := (readsNode_iff bound down indices).mp read
      intro r mem
      rw [HostHintSnapshot.liveInputs] at mem
      rcases List.mem_append.mp mem with here | later
      · obtain ⟨s,used,rfl⟩ := List.mem_map.mp here
        obtain ⟨i,inside,rfl⟩ := List.mem_map.mp used
        have atWord := read.2 i (List.mem_range.mp inside)
        have value := WordRecord.encode_valid (p := SP1Prime) head bytes i (by omega) bound
        have node := NodeRecord.encode_valid (p := SP1Prime) head ⟨bytes,tail⟩ bound down
        simp only [found,Option.map_some,Option.getD_some]
        refine ⟨fun _ => ?_,?_⟩
        · exact ⟨node,read.1⟩
        · simpa only [HostHintSnapshot.Shape.word,HostHintSnapshot.shape,WordRecord.encode,wordCount,
            Nat.add_left_inj,HostHintSnapshot.arrayWord_toArray,List.size_toArray] using And.intro value atWord
      · exact ih suffix _ _ (by simpa only [found,Option.map_some,Option.getD_some] using later)

/-- Target shapes read the same final immutable nodes and words as the mixed tape. -/
theorem snapshot_binds {store : Store} {head : Nat} {hints : List Bytes} {tails : List Nat}
    (walk : ReadsSnapshot SP1Prime store head hints tails) : (snapshot store head hints).Binds store := by
  constructor
  · intro r m
    obtain ⟨x,used,found⟩ := List.mem_filterMap.mp m
    split at found
    next first => exact Option.some.inj found ▸ (live_binds walk 0 x used).1 first
    next => contradiction
  · intro r m
    obtain ⟨x,used,rfl⟩ := List.mem_map.mp m
    exact (live_binds walk 0 x used).2

/-- All node and word readers refer to the same final immutable store, including unreachable history. -/
theorem native_demand {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    ∃ cursor, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some cursor ∧
      let demand := collect (history image source events) (snapshot cursor.1 cursor.2 target.host.io.hints)
      demand.Binds cursor.1 ∧ Extends (ofList source.host.io.hints).1 cursor.1 := by
  obtain ⟨cursor,_,finish,_,walk⟩ := admissibleExecution_hintSnapshot run
  have calls := (history_binds run finish).2
  have ending := snapshot_binds walk
  obtain ⟨_,_,after,_,init,_,_,_,_,_,other,ext,_⟩ := admissibleExecution_hintInventory run 0
  cases Option.some.inj (finish.symm.trans other)
  cases Option.some.inj init
  refine ⟨cursor,finish,⟨?_,?_⟩,ext⟩
  · intro r used
    rcases List.mem_append.mp used with prior | last
    · obtain ⟨q,atCall,member⟩ := List.mem_flatMap.mp prior
      exact (calls q atCall).1 r member
    · exact ending.1 r last
  · intro r used
    rcases List.mem_append.mp used with prior | last
    · obtain ⟨q,atCall,member⟩ := List.mem_flatMap.mp prior
      exact (calls q atCall).2 r member
    · exact ending.2 r last

end SP1Clean.TraceGen.HintQueueReaders
