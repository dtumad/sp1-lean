import SP1Clean.Proofs.Completeness.WriteWitnessTape

/-! # Dispatch and queue authority at each emitted WRITE

The positional view connects the three physical projections to the same original call, guest
read and persistent store transition. A hook with no returned buffers still opens its ticket.
-/

namespace SP1Clean.WriteEffects.Witness

open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

/-- Match the original event position using the actual shard-boundary store and two clocks. -/
noncomputable def position (image : ProgramImage) (source : ExecutionSnapshot) (events : List ExecutionEvent)
    (readers : Readers) (event : ExecutionEvent) (cut : Nat) : Option Entry :=
  at? image source.host readers source.clock 0 source.realize (ofList source.host.io.hints) events (event,cut)

/-- Agreement between the dispatch ticket, all installed allocation inputs and the canonical
state of the persistent hint queue on either side of an allocating WRITE. -/
structure AllocatedAt (entry : Entry) (batch : Batch) (readers : Readers) (prior clock : Nat) (before after : Store × Nat) : Prop where
  /-- The exact open, node, seed and word inputs carried by the collected entry. -/
  rows : entry.allocation = some (batch.rows prior clock before readers)
  /-- The original dispatcher authorizes precisely the ticket consumed by the physical open row. -/
  ticket : (batch.openRow prior clock before.1 before.2).ticket = entry.dispatch.ticket entry.dispatch.flags
  /-- The opening component accepts its clock and pointer columns. -/
  valid : (batch.openRow prior clock before.1 before.2).Valid
  /-- The queue output uses the actual cursor reached by mixed execution. -/
  outgoing : (batch.openRow prior clock before.1 before.2).outgoing = HostHintQueue.State.encode clock after.2 after.1.size
  /-- The native allocation order and persistent node values are the actual semantic prepend. -/
  stored : after = prepend before.1 before.2 batch.buffers
  /-- All fresh pointers and node byte lengths fit their original encodings. -/
  capacity : before.1.size + batch.buffers.length < 2^48 ∧ ∀ bytes ∈ batch.buffers, bytes.length < 2^48
  /-- The physically emitted node and padded-word payloads bind every persistent extension. -/
  publishes : batch.Publishes clock before after.1

/-- Every WRITE contributes one packet and valid dispatcher at its actual cut. Queue work is
present exactly for the semantic allocation route and uses that same read, clock and store. -/
theorem native_position {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {call : CoreSyscallEvent} {cut : Nat} (present : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    ∃ current next cursor after length buffer entry,
      executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events (cut+1) = some next ∧
      storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut) (ofList source.host.io.hints) = some cursor ∧
      storeAfter? (policy SP1Prime image) image.program source.realize (events.take (cut+1)) (ofList source.host.io.hints) = some after ∧
      WriteObservations.read? current.sail call = some (length,buffer) ∧
      position image source events readers (.syscall call) cut = some entry ∧ entry.packet = (length,buffer) ∧
      let earlier := WriteStreams.fromEndpoints source.host current.host
      let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
      let allocation := batchFor (WriteRoute.ofDescriptor call.arg1) earlier current.host bytes
      let prior := (events.take cut).foldl advanceQueueClock 0
      entry.dispatch = dispatchRow call.arg1 call.arg2 length current.clock ((events.take cut).foldl advanceWriteClock source.clock)
        earlier current.host cursor.1 ∧ entry.dispatch.Valid ∧
      entry.allocation = allocation.map (fun b => b.rows prior current.clock cursor readers) ∧
      ∀ batch, allocation = some batch → AllocatedAt entry batch readers prior current.clock cursor after := by
  obtain ⟨current,next,length,buffer,cursor,after,reached,stopped,read,stored,advanced,_,_,eligible⟩ := native_store_at run present write
  obtain ⟨current',_,length',buffer',cursor',atCurrent,_,otherRead,otherStore,valid,_⟩ := native_dispatch_at run present write
  cases Option.some.inj (reached.symm.trans atCurrent)
  cases Option.some.inj (stored.symm.trans otherStore)
  cases Option.some.inj (read.symm.trans otherRead)
  let earlier := WriteStreams.fromEndpoints source.host current.host
  let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
  let allocation := batchFor (WriteRoute.ofDescriptor call.arg1) earlier current.host bytes
  let prior := (events.take cut).foldl advanceQueueClock 0
  let dispatch := dispatchRow call.arg1 call.arg2 length current.clock ((events.take cut).foldl advanceWriteClock source.clock)
    earlier current.host cursor.1
  let entry : Entry := ⟨(length,buffer),dispatch,allocation.map (fun b => b.rows prior current.clock cursor readers)⟩
  have emitted : position image source events readers (.syscall call) cut = some entry := by
    simp [position,at?,reached,stored,WriteObservations.packetAt?,write,read,emit,entry,allocation,earlier,bytes,prior,dispatch]
  refine ⟨current,next,cursor,after,length,buffer,entry,reached,stopped,stored,advanced,read,emitted,rfl,rfl,valid,rfl,?_⟩
  intro batch active
  obtain ⟨checked,ticket,outgoing,_,_,same,fits,sizes,publications⟩ := eligible batch active
  have rows : entry.allocation = some (batch.rows prior current.clock cursor readers) := by
    change allocation.map _ = _
    rw [show allocation = some batch from active]
    rfl
  exact ⟨rows,ticket,checked,outgoing,same,⟨fits,sizes⟩,publications⟩

/-- A chronological dispatcher is present exactly once for every WRITE, including calls with
zero requested bytes and hooks that return no nodes. Other CPU and host events emit no row. -/
theorem native_position_active {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {event : ExecutionEvent} {cut : Nat} (present : events[cut]? = some event) :
    let result := position image source events readers event cut
    result.isSome = WriteObservations.isWriteCall event ∧ ∀ entry ∈ result, entry.dispatch.Valid := by
  obtain ⟨current,cursor,_,path,stored,_⟩ := admissibleExecution_hintInventory run cut
  have reached := path.replay
  change executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current at reached
  cases event with
  | ordinary => simp [position,at?,reached,stored,WriteObservations.packetAt?,emit,WriteObservations.isWriteCall]
  | syscall call =>
    by_cases write : call.rawCode = SyscallKind.write.code
    · obtain ⟨_,_,_,_,_,_,entry,_,_,_,_,_,emitted,_,_,valid,_⟩ := native_position run readers present write
      simp [emitted,WriteObservations.isWriteCall,write,valid]
    · simp [position,at?,reached,stored,WriteObservations.packetAt?,emit,WriteObservations.isWriteCall,write]

end SP1Clean.WriteEffects.Witness
