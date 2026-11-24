import SP1Clean.Proofs.Completeness.WriteWitnessAllocation
import SP1Clean.Proofs.Completeness.WriteProbeDemand

/-! # Chronological WRITE observation and allocation witness

Each CPU event advances the Sail replay and persistent hint cursor once. A single successful
guest read supplies the packet, dispatcher and optional allocator rows for that position.
The positional view is used to identify emitted rows in proofs.
-/

namespace SP1Clean.WriteEffects.Witness

open Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- The rows attached to a single observed WRITE. Empty and ignored WRITEs retain their packet
and dispatch row. Empty hook replies retain their allocation open row. -/
structure Entry where
  /-- The length register and original aligned buffer reads. -/
  packet : WriteObservations.Packet
  /-- The physical row using this exact observation and incoming queue. -/
  dispatch : Dispatch F
  /-- All fresh queue rows, present exactly on the allocating routes. -/
  allocation : Option BatchRows

/-- Assemble the three physical views of an observed syscall from its single guest read. -/
def emit (readers : Readers) (origin : HostState) (dispatchClock queueClock : Nat) (current : ExecutionState)
    (cursor : HintQueue.Store × Nat) : ExecutionEvent → Option WriteObservations.Packet → Option Entry
  | .syscall call, some packet =>
    let earlier := WriteStreams.fromEndpoints origin current.host
    let bytes := WriteObservations.payload packet.2 call.arg2.toNat packet.1.toNat
    let allocation := batchFor (WriteRoute.ofDescriptor call.arg1) earlier current.host bytes
    some ⟨packet, dispatchRow call.arg1 call.arg2 packet.1 current.clock dispatchClock earlier current.host cursor.1,
      allocation.map (fun b => b.rows queueClock current.clock cursor readers)⟩
  | _, _ => none

private def record {α : Type} (entry : Option α) (earlier : List α) : List α :=
  match entry with
  | some e => e :: earlier
  | none => earlier

private abbrev Emitter (α : Type) := Nat → Nat → ExecutionState → HintQueue.Store × Nat → ExecutionEvent → Option WriteObservations.Packet → Option α

private noncomputable def visit? {α : Type} (image : ProgramImage) (observe : Emitter α) :
    Nat → Nat → ExecutionState → HintQueue.Store × Nat → List α → List ExecutionEvent → Option (List α)
  | _, _, _, _, earlier, [] => some earlier.reverse
  | dispatchClock, queueClock, current, cursor, earlier, event :: rest => do
    let hostPolicy := policy SP1Prime image
    let next ← replayStep? hostPolicy image.program current event
    let advanced ← HintQueue.advance? current.host next.host cursor event
    let observation ← WriteObservations.packetAt? current.sail event
    let entry := observe dispatchClock queueClock current cursor event observation
    visit? image observe (advanceWriteClock dispatchClock event) (advanceQueueClock queueClock event)
      next advanced (record entry earlier) rest

/-- Tail-recursive collector carrying the current execution state, persistent store cursor and
two clocks. The accumulator stores only emitted rows and is reversed once at the endpoint. -/
noncomputable def collect? (image : ProgramImage) (origin : HostState) (readers : Readers)
    (dispatchClock queueClock : Nat) (source : ExecutionState) (cursor : HintQueue.Store × Nat) (events : List ExecutionEvent) :
    Option (List Entry) := visit? image (emit readers origin) dispatchClock queueClock source cursor [] events

private theorem visit_map {α β : Type} (image : ProgramImage) (observe : Emitter α) (f : α → β)
    (d q : Nat) (source : ExecutionState) (cursor : HintQueue.Store × Nat) (earlier : List α) (events : List ExecutionEvent) :
    visit? image (fun a b s c e p => (observe a b s c e p).map f) d q source cursor (earlier.map f) events =
      (visit? image observe d q source cursor earlier events).map (List.map f) := by
  induction events generalizing d q source cursor earlier with
  | nil => simp [visit?,List.map_reverse]
  | cons event rest ih =>
    simp only [visit?]
    cases step : replayStep? (policy SP1Prime image) image.program source event with
    | none => rfl
    | some next =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases advanced : HintQueue.advance? source.host next.host cursor event with
      | none => rfl
      | some after =>
        simp only [Option.bind_some]
        cases observed : WriteObservations.packetAt? source.sail event with
        | none => rfl
        | some packet =>
          have row : record ((observe d q source cursor event packet).map f) (earlier.map f) =
              (record (observe d q source cursor event packet) earlier).map f := by
            cases observe d q source cursor event packet <;> rfl
          simp only [Option.bind_some,row]
          exact ih _ _ next after (record (observe d q source cursor event packet) earlier)

private def dispatchOnly (origin : HostState) (d : Nat) (_ : Nat) (current : ExecutionState) (cursor : HintQueue.Store × Nat) :
    ExecutionEvent → Option WriteObservations.Packet → Option (Dispatch F)
  | .syscall call, some packet => some (dispatchRow call.arg1 call.arg2 packet.1 current.clock d
      (WriteStreams.fromEndpoints origin current.host) current.host cursor.1)
  | _, _ => none

/-- The dispatcher-only projection of the shared traversal needs no queue reader multiplicities. -/
noncomputable def _root_.SP1Clean.WriteEffects.dispatchTape? (image : ProgramImage) (origin : HostState) (d : Nat) (source : ExecutionState)
    (cursor : HintQueue.Store × Nat) (events : List ExecutionEvent) : Option (List (Dispatch F)) :=
  visit? image (dispatchOnly origin) d 0 source cursor [] events

/-- The dispatch table consumes precisely the projection of any full collection at these
clocks, independently of node and word query multiplicities. -/
theorem dispatch_projection (image : ProgramImage) (origin : HostState) (readers : Readers)
    (d : Nat) (source : ExecutionState) (cursor : HintQueue.Store × Nat) (events : List ExecutionEvent) :
    dispatchTape? image origin d source cursor events =
      (collect? image origin readers d 0 source cursor events).map (List.map Entry.dispatch) := by
  have project : dispatchOnly origin = fun a b s c e obs => (emit readers origin a b s c e obs).map Entry.dispatch := by
    funext a b s c e obs
    cases e <;> cases obs <;> rfl
  rw [dispatchTape?,project,collect?]
  exact visit_map image (emit readers origin) Entry.dispatch d 0 source cursor [] events

/-- Proof-oriented characterization at an original event position. -/
noncomputable def at? (image : ProgramImage) (origin : HostState) (readers : Readers) (dispatchClock queueClock : Nat)
    (source : ExecutionState) (cursor : HintQueue.Store × Nat) (events : List ExecutionEvent) (position : ExecutionEvent × Nat) : Option Entry := do
  let hostPolicy := policy SP1Prime image
  let current ← executionTrajectory hostPolicy image.program source events position.2
  let before ← HintQueue.storeAfter? hostPolicy image.program source (events.take position.2) cursor
  let observed ← WriteObservations.packetAt? current.sail position.1
  emit readers origin ((events.take position.2).foldl advanceWriteClock dispatchClock)
    ((events.take position.2).foldl advanceQueueClock queueClock) current before position.1 observed

private theorem at_succ (image : ProgramImage) (origin : HostState) (readers : Readers) (d q : Nat)
    (source next : ExecutionState) (cursor advanced : HintQueue.Store × Nat) (head : ExecutionEvent) (rest : List ExecutionEvent)
    (step : replayStep? (policy SP1Prime image) image.program source head = some next)
    (advance : HintQueue.advance? source.host next.host cursor head = some advanced) (event : ExecutionEvent) (i : Nat) :
    at? image origin readers d q source cursor (head :: rest) (event,i+1) =
      at? image origin readers (advanceWriteClock d head) (advanceQueueClock q head) next advanced rest (event,i) := by
  simp [at?, executionTrajectory, replayEvents?, step, HintQueue.storeAfter?, advance]

private theorem packet_emitted (readers : Readers) (origin : HostState) (d q : Nat) (current : ExecutionState)
    (cursor : HintQueue.Store × Nat) (head : ExecutionEvent) (obs : Option WriteObservations.Packet)
    (read : WriteObservations.packetAt? current.sail head = some obs) :
    (emit readers origin d q current cursor head obs).map Entry.packet = obs := by
  cases head with
  | ordinary => cases read; rfl
  | syscall call => cases obs <;> rfl

/-- A whole successful replay preserves source order, every repeated observation and the
actual list of collected packets. Prefix replay is used only in the conclusion about positions. -/
private theorem visit_spec {image : ProgramImage} (origin : HostState) (readers : Readers) {source : ExecutionState}
    {events : List ExecutionEvent} (d q : Nat) {cursor final : HintQueue.Store × Nat}
    (store : HintQueue.storeAfter? (policy SP1Prime image) image.program source events cursor = some final)
    {packets : List WriteObservations.Packet}
    (reads : WriteObservations.packets? (policy SP1Prime image) image.program source events = some packets) (earlier : List Entry) :
    let entries := events.zipIdx.filterMap (at? image origin readers d q source cursor events)
    visit? image (emit readers origin) d q source cursor earlier events = some (earlier.reverse ++ entries) ∧ entries.map Entry.packet = packets := by
  induction events generalizing source d q cursor packets earlier with
  | nil => cases reads; exact ⟨(congrArg some (List.append_nil _)).symm,rfl⟩
  | cons head rest ih =>
    simp only [HintQueue.storeAfter?,Option.bind_eq_bind,Option.bind_eq_some_iff] at store
    obtain ⟨next,step,advanced,advance,remain⟩ := store
    simp only [WriteObservations.packets?,step,Option.bind_eq_bind,Option.bind_some,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at reads
    obtain ⟨observation,observed,tail,tailRead,rfl⟩ := reads
    obtain ⟨compiled,owned⟩ := ih (advanceWriteClock d head) (advanceQueueClock q head) remain tailRead (record (emit readers origin d q source cursor head observation) earlier)
    dsimp only
    rw [List.zipIdx_cons',List.filterMap_cons,List.filterMap_map]
    have align : at? image origin readers d q source cursor (head :: rest) ∘ Prod.map id (· + 1) =
        at? image origin readers (advanceWriteClock d head) (advanceQueueClock q head) next advanced rest := by
      funext ⟨e,i⟩
      exact at_succ image origin readers d q source next cursor advanced head rest step advance e i
    have first : at? image origin readers d q source cursor (head :: rest) (head,0) =
        emit readers origin d q source cursor head observation := by
      simp [at?, executionTrajectory, replayEvents?, HintQueue.storeAfter?, observed]
    rw [align,first]
    have packet := packet_emitted readers origin d q source cursor head observation observed
    simp only [visit?,step,advance,observed,compiled,Option.bind_eq_bind,Option.bind_some]
    cases used : emit readers origin d q source cursor head observation with
    | none => rw [used] at packet; cases packet; exact ⟨rfl,owned⟩
    | some e =>
      rw [used] at packet
      cases packet
      exact ⟨by simp [record, List.append_assoc], congrArg (e.packet :: ·) owned⟩

/-- All packet, dispatcher and allocator rows are collected in one traversal of the semantic event tape. -/
noncomputable def native? (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (readers : Readers) : Option (List Entry) :=
  collect? image source.host readers source.clock 0 source.realize (HintQueue.ofList source.host.io.hints) events

/-- The initial state, store and clocks of the native shard give a total chronological collection
whose packet projection is exactly the independently specified ordered observation tape. -/
theorem native_collect {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) :
    let entries := events.zipIdx.filterMap (at? image source.host readers source.clock 0 source.realize
      (HintQueue.ofList source.host.io.hints) events)
    native? image source events readers = some entries ∧
      WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some (entries.map Entry.packet) := by
  obtain ⟨_,store,_⟩ := HintQueue.storeAfter_of_path run.1.2 (HintQueue.ofList_wellFormed _) (HintQueue.ofList_represents _)
  obtain ⟨packets,reads⟩ := WriteObservations.admissible_packets run
  obtain ⟨built,observed⟩ := visit_spec source.host readers source.clock 0 store reads []
  exact ⟨built, observed ▸ reads⟩

end SP1Clean.WriteEffects.Witness
