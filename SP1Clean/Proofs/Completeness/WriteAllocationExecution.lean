import SP1Clean.Proofs.Completeness.WriteAllocationBatch
import SP1Clean.Proofs.Completeness.WriteDispatchRows

/-! # Allocation authority in the mixed WRITE dispatcher

The descriptor and the actual consumed hook reply determine whether a WRITE allocates.
The ticket is the same message emitted on the dispatch row's queue-effect channel.
-/

namespace SP1Clean.WriteAllocation

open Semantics Machine FormalModel.Shard TraceGen WriteEffects

private abbrev F := ZMod SP1Prime

/-- All queue work authorized by the descriptor, including hooks returning zero buffers. -/
def batchAt (route : WriteRoute) (hookIndex : Nat) (host : HostState) (bytes : Bytes) : Option Batch :=
  match route with
  | .hint => some (.direct bytes)
  | .hook _ => some (.hook hookIndex bytes.length (route.allocations host bytes))
  | _ => none

/-- Characterization of an allocating WRITE using its actual preceding host transcript. -/
def batchFor (route : WriteRoute) (earlier : WriteStreams) (host : HostState) (bytes : Bytes) : Option Batch :=
  batchAt route earlier.hooks.length host bytes

/-- The dispatch gate is active exactly once for each allocating call, including an empty hook reply. -/
theorem dispatch_allocation_gate (fd address len : BitVec 64) (clk previous : Nat) (earlier : WriteStreams)
    (host : HostState) (store : HintQueue.Store) (bytes : Bytes) :
    let row := dispatchRow fd address len clk previous earlier host store
    row.flags.direct + row.flags.hook = if (batchFor (WriteRoute.ofDescriptor fd) earlier host bytes).isSome then (1 : F) else 0 := by
  cases route : WriteRoute.ofDescriptor fd <;> simp [dispatchRow,dispatchColumns,route,routeFlags,DispatchFlags.hook,batchFor,batchAt]

/-- Every open row consumes the actual call's ticket and prepends precisely the semantic buffers. -/
theorem dispatch_allocation_ticket (fd address len : BitVec 64) (clk previous : Nat) (earlier : WriteStreams)
    (host : HostState) (store : HintQueue.Store) (bytes : Bytes) (size : bytes.length = len.toNat) {batch : Batch}
    (active : batchFor (WriteRoute.ofDescriptor fd) earlier host bytes = some batch) :
    let row := dispatchRow fd address len clk previous earlier host store
    row.ticket row.flags = batch.ticket clk store.size ∧ batch.buffers = (WriteRoute.ofDescriptor fd).allocations host bytes := by
  let row := dispatchRow fd address len clk previous earlier host store
  have length : row.length = Address.ofNat len.toNat := dispatchRow_length fd address len clk previous earlier host store
  have three (a : fields 3 F) : #v[a[0],a[1],a[2]] = a := by
    ext i hi
    interval_cases i <;> rfl
  have returns : ((host.replies.head?.map (·.hints.length)).getD 0) =
      ((host.replies.head?.map HookReply.hints).getD []).length := by
    cases host.replies <;> rfl
  change row.ticket row.flags = _ ∧ _
  cases route : WriteRoute.ofDescriptor fd <;> simp [batchFor,batchAt,route] at active
  all_goals subst batch
  all_goals simp only [Dispatch.ticket,length]
  all_goals simp [Dispatch.owner,row,dispatchRow,dispatchColumns,route,routeFlags,DispatchFlags.hook,
    Batch.ticket,Batch.buffers,WriteRoute.allocations,threeLimbs,three,size,returns,finalCursor]
  all_goals first | exact ⟨rfl, rfl⟩ | rfl

/-- Recover the allocation authority from the actual WRITE row at any cut of a mixed execution.
Its direct bytes come from the guest memory read and its hook ordinal comes from the host prefix. -/
theorem native_allocation_ticket_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call))
    (write : call.rawCode = SyscallKind.write.code) :
    ∃ current length buffer cursor,
      executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current ∧
      WriteObservations.read? current.sail call = some (length,buffer) ∧
      HintQueue.storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut)
        (HintQueue.ofList source.host.io.hints) = some cursor ∧
      let earlier := WriteStreams.fromEndpoints source.host current.host
      let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
      let route := WriteRoute.ofDescriptor call.arg1
      let batch := batchFor route earlier current.host bytes
      let row := dispatchRow call.arg1 call.arg2 length current.clock ((events.take cut).foldl advanceWriteClock source.clock)
        earlier current.host cursor.1
      row.Valid ∧ (row.flags.direct + row.flags.hook = if batch.isSome then 1 else 0) ∧
        ∀ b, batch = some b → row.ticket row.flags = b.ticket current.clock cursor.1.size ∧
          b.buffers = route.allocations current.host bytes := by
  obtain ⟨current, _, length, buffer, cursor, atCut, _, read, store, valid, _⟩ := native_dispatch_at run present write
  obtain ⟨_, _, _, _, count, _⟩ := WriteObservations.read?_eq_some_iff.mp read
  refine ⟨current,length,buffer,cursor,atCut,read,store,valid,dispatch_allocation_gate ..,?_⟩
  intro batch active
  exact dispatch_allocation_ticket _ _ _ _ _ _ _ _ _ (WriteObservations.payload_length count) active

end SP1Clean.WriteAllocation
