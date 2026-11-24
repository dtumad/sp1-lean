import SP1Clean.Proofs.Completeness.WriteAllocationExecution
import SP1Clean.Proofs.Completeness.WriteAllocationStoredWords

/-! # WRITE allocation rows over the actual persistent store

Every allocating dispatcher advances the same store projection used by HINT_READ.
The previous queue clock is computed from the complete event prefix, including
length queries, pops and hook calls that return an empty list.
-/

namespace SP1Clean.WriteAllocation

open Semantics Machine FormalModel.Shard TraceGen WriteEffects HintQueue

private abbrev F := ZMod SP1Prime

/-- The private queue state is reissued by both hint calls and by each allocating WRITE. -/
def usesQueue (call : CoreSyscallEvent) : Bool :=
  call.rawCode == SyscallKind.hintRead.code || call.rawCode == SyscallKind.hintLength.code ||
    (call.rawCode == SyscallKind.write.code && match WriteRoute.ofDescriptor call.arg1 with
      | .hint | .hook _ => true
      | _ => false)

/-- Timestamp of the most recent call using the private queue, initially zero at the boundary. -/
def advanceQueueClock (previous : Nat) : ExecutionEvent → Nat
  | .ordinary => previous
  | .syscall call => if usesQueue call then call.clock else previous

/-- Every queue clock accumulated on an execution prefix is zero or precedes its endpoint. -/
theorem queue_clock_before {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} (path : ExecutionPath policy program source events target)
    (initial : Nat) (ordered : initial = 0 ∨ initial < source.clock) :
    events.foldl advanceQueueClock initial = 0 ∨ events.foldl advanceQueueClock initial < target.clock := by
  induction path generalizing initial with
  | nil => exact ordered
  | @cons before middle last event rest step _ ih =>
    apply ih
    have stamp := step.startsAt
    have stop := step.clock
    cases event with
    | ordinary =>
      simp only [ExecutionEvent.duration_ordinary] at stop
      change initial = 0 ∨ initial < middle.clock
      omega
    | syscall call =>
      change call.clock = before.clock at stamp
      simp only [ExecutionEvent.duration_syscall] at stop
      simp only [advanceQueueClock]
      split <;> omega

/-- The actual final queue-access clock fits the released state encoding, including a
segment whose queue carried the initial zero clock throughout. -/
theorem final_queue_clock_fits {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    events.foldl advanceQueueClock 0 < 2^48 := by
  have order := queue_clock_before run.1.2 0 (Or.inl rfl)
  have stop := run.2.2.2.2.2.1
  change target.clock < 2^48 at stop
  change events.foldl advanceQueueClock 0 = 0 ∨ events.foldl advanceQueueClock 0 < target.clock at order
  omega

private theorem write_advances {current next : ExecutionState} {route : WriteRoute} {bytes : Bytes}
    {call : CoreSyscallEvent} (effect : route.Effect current.host bytes next.host) (write : call.rawCode = SyscallKind.write.code)
    (cursor : Store × Nat) :
    advance? current.host next.host cursor (.syscall call) = some (prepend cursor.1 cursor.2 (route.allocations current.host bytes)) := by
  have decoded := (SyscallKind.decode?_eq_some_iff call.rawCode .write).mpr write.symm
  simp [advance?, decoded,HostState.hintUpdate,effect.queue,Update.apply?]

/-- Every allocating mixed WRITE has the actual pre- and post-call cursor, a valid open row,
and enough space for every node and every individual buffer. No allocator premise is required. -/
theorem native_store_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    ∃ current next length buffer cursor after,
      executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events (cut+1) = some next ∧
      WriteObservations.read? current.sail call = some (length,buffer) ∧
      storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut) (ofList source.host.io.hints) = some cursor ∧
      storeAfter? (policy SP1Prime image) image.program source.realize (events.take (cut+1)) (ofList source.host.io.hints) = some after ∧
      Represents cursor.1 cursor.2 current.host.io.hints ∧ Represents after.1 after.2 next.host.io.hints ∧
      let earlier := WriteStreams.fromEndpoints source.host current.host
      let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
      let route := WriteRoute.ofDescriptor call.arg1
      after = prepend cursor.1 cursor.2 (route.allocations current.host bytes) ∧
      ∀ batch, batchFor route earlier current.host bytes = some batch →
        let prior := (events.take cut).foldl advanceQueueClock 0
        let row := batch.openRow prior current.clock cursor.1 cursor.2
        let dispatch := dispatchRow call.arg1 call.arg2 length current.clock
          ((events.take cut).foldl advanceWriteClock source.clock) earlier current.host cursor.1
        row.Valid ∧ row.ticket = dispatch.ticket dispatch.flags ∧
          row.outgoing = HostHintQueue.State.encode current.clock after.2 after.1.size ∧
          row.first = batch.cursorAt current.clock cursor.2 cursor.1.size 0 ∧
          row.last = batch.cursorAt current.clock cursor.2 cursor.1.size batch.buffers.length ∧
          after = prepend cursor.1 cursor.2 batch.buffers ∧ cursor.1.size + batch.buffers.length < 2^48 ∧
          (∀ b ∈ batch.buffers, b.length < 2^48) ∧ batch.Publishes current.clock cursor after.1 := by
  obtain ⟨current,next,length,buffer,read,atCurrent,atNext,effect,_⟩ := groups_of_admissibleExecution run present write
  obtain ⟨left,cursor,_,beforePath,beforeStore,rep,_⟩ := admissibleExecution_hintInventory run cut
  obtain ⟨right,after,_,post,afterStore,repAfter,_,_,space,_⟩ := admissibleExecution_hintInventory run (cut+1)
  obtain rfl : left = current := Option.some.inj (beforePath.replay.symm.trans atCurrent)
  obtain rfl : right = next := Option.some.inj (post.replay.symm.trans atNext)
  obtain ⟨_,_,_,_,count,_⟩ := WriteObservations.read?_eq_some_iff.mp read
  have replay := executionTrajectory_succ (policy SP1Prime image) image.program source.realize events present
  rw [atNext,atCurrent,Option.bind_some] at replay
  let route := WriteRoute.ofDescriptor call.arg1
  let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
  obtain ⟨inTape,event⟩ := List.getElem?_eq_some_iff.mp present
  have built := afterStore
  rw [List.take_succ_eq_append_getElem inTape,event,storeAfter_append beforePath,beforeStore,Option.bind_some] at built
  simp only [storeAfter?,replay.symm,Option.bind_eq_bind,Option.bind_some,write_advances effect write cursor] at built
  have postState : after = prepend cursor.1 cursor.2 (route.allocations left.host bytes) := (Option.some.inj built).symm
  have window := run.1.2.clock_at present atCurrent
  have stop := run.2.2.2.2.2.1
  change left.clock + 264 ≤ target.clock at window
  change target.clock < 2^48 at stop
  have phase := (run.2.1 cut left (.syscall call) present atCurrent).1
  change left.clock % 8 = 1 at phase
  have ordered := queue_clock_before beforePath 0 (Or.inl rfl)
  have budget := post.resources_append (events.drop (cut+1))
  rw [List.take_append_drop] at budget
  have paid := run.2.2.1
  rw [budget] at paid
  have live := post.endpoint_fits run.2.2.2.1 paid.left .liveHintBytes
  change (right.host.io.hints.map List.length).sum ≤ SP1Prime - 1 at live
  refine ⟨left,right,length,buffer,cursor,after,atCurrent,atNext,read,beforeStore,afterStore,rep,repAfter,postState,?_⟩
  dsimp only
  intro batch active
  obtain ⟨ticket,buffers⟩ := dispatch_allocation_ticket call.arg1 call.arg2 length left.clock ((events.take cut).foldl advanceWriteClock source.clock)
    (WriteStreams.fromEndpoints source.host left.host) left.host cursor.1 bytes (WriteObservations.payload_length count) active
  have same : after = prepend cursor.1 cursor.2 batch.buffers := buffers ▸ postState
  obtain ⟨valid,first,last,outgoing⟩ := batch.openRow_valid ((events.take cut).foldl advanceQueueClock 0) left.clock
    cursor.1 cursor.2 (by omega) (by omega)
  have capacity : cursor.1.size + batch.buffers.length < 2^48 := by
    rwa [same,prepend_size] at space
  have sizes (b : Bytes) (member : b ∈ batch.buffers) : b.length < 2^48 := by
    have mem : b ∈ right.host.io.hints := by
      rw [effect.queue]
      exact List.mem_append_left _ (buffers ▸ member)
    exact (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) mem)).trans_lt
      (live.trans_lt (by decide))
  refine ⟨valid,ticket.symm,same ▸ outgoing,first,last,same,capacity,sizes,?_⟩
  rw [same]
  exact batch.publishes_prepend left.clock cursor.1 cursor.2 left.host.io.hints rep capacity sizes

end SP1Clean.WriteAllocation
