import SP1Clean.Proofs.Operations.WriteClassifiedRoute
import SP1Clean.Proofs.Completeness.WriteDestination
import SP1Clean.Native.Operations.WriteCursorBoundary

/-! # Chronological dispatch rows from mixed execution

The preceding cursor uses the most recent WRITE clock even when ordinary instructions or
other host calls intervene. Every byte counter and reply ordinal comes from the actual
host prefix. A direct hint receives the next permanent identity from the allocation frontier.
-/

namespace SP1Clean.WriteEffects

open Semantics Machine FormalModel.Shard TraceGen Soundness Soundness.Target

private abbrev F := ZMod SP1Prime

/-- Only WRITE advances the chronological dispatch cursor. -/
def advanceWriteClock (previous : Nat) : ExecutionEvent → Nat
  | .syscall call => if call.rawCode = SyscallKind.write.code then call.clock + 1 else previous
  | .ordinary => previous

/-- The actual dispatch cursor clock never passes the current CPU cut. -/
theorem dispatch_clock_le {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath policy program source events target)
    (initial : Nat) (lower : initial ≤ source.clock) : events.foldl advanceWriteClock initial ≤ target.clock := by
  induction path generalizing initial with
  | nil => exact lower
  | @cons source middle target event rest step _ ih =>
    apply ih
    have stamp := step.startsAt
    have stop := step.clock
    cases event with
    | ordinary => simp only [ExecutionEvent.duration_ordinary] at stop; exact lower.trans (by omega)
    | syscall call =>
      change call.clock = source.clock at stamp
      simp only [ExecutionEvent.duration_syscall] at stop
      simp only [advanceWriteClock]
      split <;> omega

/-- Counter consumed by this dispatch's arithmetic step. -/
def previousCount (route : WriteRoute) (earlier : WriteStreams) : Nat :=
  match route with
  | .hook _ => earlier.hooks.length
  | _ => destinationOffset route earlier

/-- Amount added to the selected stream counter. -/
def countDelta (route : WriteRoute) (length : Nat) : Nat :=
  match route with
  | .stdout | .stderr | .publicValues => length
  | .hook _ => 1
  | .ignored | .hint => 0

/-- The existing dispatch encoding with its natural positions already computed. -/
def dispatchColumns (fd address length : BitVec 64) (callClock previousClock : Nat) (incoming : StreamCursor F)
    (offset count : Nat) (host : HostState) (store : HintQueue.Store) : Dispatch F :=
  let route := WriteRoute.ofDescriptor fd
  let delta := countDelta route length.toNat
  let pred := address.toNat - 1
  let pack := effectRows (p := SP1Prime) callClock fd address length []
  { request := pack.1, flags := routeFlags route, previous := incoming
    clockGap := Address.ofNat (callClock - previousClock), nextClock := Address.ofNat (callClock + 1)
    payloadLength := Address.ofNat length.toNat, basePosition := Address.ofNat offset
    baseCounter := Address.ofNat count, delta := Address.ofNat delta, beforeAddress := Address.ofNat pred
    lastAddress := Address.ofNat (pred + length.toNat), endPosition := Address.ofNat (offset + length.toNat)
    nextCounter := Address.ofNat (count + delta), pointer := Address.ofNat (store.size + 1)
    returned := Address.ofNat ((host.replies.head?.map (·.hints.length)).getD 0) }

/-- Construct the original dispatch row directly from running stream lengths. -/
def StreamCounts.dispatch (earlier : StreamCounts) (fd address length : BitVec 64) (callClock previousClock : Nat)
    (host : HostState) (store : HintQueue.Store) : Dispatch F :=
  let route := WriteRoute.ofDescriptor fd
  let offset := match route with
    | .stdout => earlier.stdout
    | .stderr => earlier.stderr
    | .publicValues => earlier.publicValues
    | _ => 0
  let count := match route with
    | .hook _ => earlier.hooks
    | _ => offset
  let incoming : StreamCursor F := ⟨Address.ofNat previousClock,Address.ofNat earlier.stdout,Address.ofNat earlier.stderr,
    Address.ofNat earlier.publicValues,Address.ofNat earlier.hooks⟩
  dispatchColumns fd address length callClock previousClock incoming offset count host store

/-- Populate the dispatcher from the semantic host transcript, including the actual reply count
and the allocation frontier after previously consumed nodes. -/
def dispatchRow (fd address length : BitVec 64) (callClock previousClock : Nat) (earlier : WriteStreams)
    (host : HostState) (store : HintQueue.Store) : Dispatch F :=
  let route := WriteRoute.ofDescriptor fd
  dispatchColumns fd address length callClock previousClock (finalCursor previousClock earlier)
    (destinationOffset route earlier) (previousCount route earlier) host store

/-- Running counters encode exactly the original dispatch row derived from the full transcript. -/
theorem StreamCounts.dispatch_ofStreams (earlier : WriteStreams) (fd address length : BitVec 64) (clk prev : Nat)
    (host : HostState) (store : HintQueue.Store) :
    (ofStreams earlier).dispatch fd address length clk prev host store = dispatchRow fd address length clk prev earlier host store := by
  cases route : WriteRoute.ofDescriptor fd <;> simp [dispatch,dispatchRow,ofStreams,finalCursor,previousCount,destinationOffset,route]

/-- The dispatch ticket uses the low three little-endian limbs of the observed x12. -/
theorem dispatchRow_length (fd address len : BitVec 64) (clk prev : Nat) (earlier : WriteStreams)
    (host : HostState) (store : HintQueue.Store) :
    (dispatchRow fd address len clk prev earlier host store).length = Address.ofNat len.toNat := by
  change #v[(bitVecToWord (p := SP1Prime) len)[0], (bitVecToWord (p := SP1Prime) len)[1],
    (bitVecToWord (p := SP1Prime) len)[2]] = _
  simp [bitVecToWord, Address.ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem three_eq (x : fields 3 F) : threeLimbs (fun i => x[i.val]) = x := by
  ext i inside
  interval_cases i <;> rfl

private theorem selections (route : WriteRoute) (earlier : WriteStreams) (clock : Nat) (d : Dispatch F)
    (prior : d.previous = finalCursor clock earlier) (n : Nat) (length : d.length = Address.ofNat n) :
    d.outputPosition (routeFlags route) = Address.ofNat (destinationOffset route earlier) ∧
    d.oldCounter (routeFlags route) = Address.ofNat (previousCount route earlier) ∧
    d.increment (routeFlags route) = Address.ofNat (countDelta route n) := by
  have low (x : fields 3 F) : #v[x[0], x[1], x[2]] = x := three_eq x
  have zero : Address.ofNat (p := SP1Prime) 0 = #v[0,0,0] := by decide
  have one : Address.ofNat (p := SP1Prime) 1 = #v[1,0,0] := by decide
  cases route <;> simp [routeFlags, Dispatch.outputPosition, Dispatch.oldCounter, Dispatch.increment, DispatchFlags.hook,
    countDelta, previousCount, destinationOffset, prior, finalCursor, length, threeLimbs, low, zero, one]

/-- All arithmetic witness fields represent their exact natural values, including the upper
endpoint for an empty guest buffer. -/
theorem dispatchRow_valid (fd address length : BitVec 64) (clk previousClock : Nat) (earlier : WriteStreams)
    (host : HostState) (store : HintQueue.Store) (order : previousClock ≤ clk) (clockFit : clk + 1 < 2^48)
    (positive : 0 < address.toNat) (guest : address.toNat + length.toNat ≤ 2^48)
    (offsetFit : destinationOffset (WriteRoute.ofDescriptor fd) earlier + length.toNat < 2^48)
    (counterFit : previousCount (WriteRoute.ofDescriptor fd) earlier + countDelta (WriteRoute.ofDescriptor fd) length.toNat < 2^48) :
    (dispatchRow fd address length clk previousClock earlier host store).Valid := by
  let route := WriteRoute.ofDescriptor fd
  let r := dispatchRow fd address length clk previousClock earlier host store
  have len : r.length = Address.ofNat length.toNat := dispatchRow_length fd address length clk previousClock earlier host store
  have select := selections route earlier previousClock r rfl length.toNat len
  have start : Address.toNat (Address.ofNat (p := SP1Prime) (address.toNat - 1)) = address.toNat - 1 :=
    Address.toNat_ofNat _ (by omega)
  have natural : (bitVecToWord (p := SP1Prime) address).toNat = address.toNat := by
    rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord]
  have one : Address.ofNat (p := SP1Prime) 1 = #v[1,0,0] := by decide
  refine ⟨?_, ?_, len.symm, select.1.symm, select.2.1.symm, select.2.2.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change routeFlags route = flagsFor ((WriteRoute.ofDescriptor (bitVecToWord (p := SP1Prime) fd).toBitVec64).tag : F)
    rw [toBitVec64_bitVecToWord]; exact (semantic_flags fd).symm
  · change (bitVecToWord (p := SP1Prime) length)[3] = 0
    simp [bitVecToWord, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt (by omega)]
    rfl
  · have sum := AddressSum.spec_ofNat (p := SP1Prime) previousClock (clk-previousClock) (by omega)
    rwa [Nat.add_sub_of_le order] at sum
  · exact one ▸ AddressSum.spec_ofNat clk 1 clockFit
  · refine ⟨Address.bounded_ofNat _, isU64_bitVecToWord _, ?_⟩
    change (bitVecToWord (p := SP1Prime) address).toNat = Address.toNat (Address.ofNat (p := SP1Prime) (address.toNat - 1)) + 1
    rw [natural, start]
    omega
  · exact AddressSum.spec_ofNat (address.toNat-1) length.toNat (by omega)
  · exact AddressSum.spec_ofNat _ _ offsetFit
  · exact AddressSum.spec_ofNat _ _ counterFit


private theorem counter_after {route : WriteRoute} {host next : HostState} {bytes : Bytes}
    (effect : route.Effect host bytes next) (earlier : WriteStreams) :
    previousCount route (earlier.append (WriteStreams.ofEvent route host bytes)) =
      previousCount route earlier + countDelta route bytes.length := by
  cases route with
  | hook fd =>
    obtain ⟨_, _, issued, _⟩ := effect
    simp [previousCount, countDelta, WriteStreams.append, WriteStreams.ofEvent, issued]
  | _ => simp [previousCount, countDelta, destinationOffset, WriteStreams.append, WriteStreams.ofEvent]

private theorem counter_le_cost (route : WriteRoute) (before after : WriteStreams) :
    previousCount route before ≤ streamCost (before.append after) := by
  have paid := count_hooks_le before.hooks
  cases route <;> simp only [previousCount, destinationOffset, streamCost, WriteStreams.append,
    List.length_append, List.map_append, List.sum_append] <;> omega

private theorem cursor_next {route : WriteRoute} {host next : HostState} {bytes : Bytes}
    (effect : route.Effect host bytes next) (earlier : WriteStreams) (previous clock : Nat) (r : Dispatch F)
    (prior : r.previous = finalCursor previous earlier) (stamp : r.nextClock = Address.ofNat (clock+1))
    (updated : r.nextCounter = Address.ofNat (previousCount route earlier + countDelta route bytes.length)) :
    r.next (routeFlags route) = finalCursor (clock+1) (earlier.append (WriteStreams.ofEvent route host bytes)) := by
  have low (x : fields 3 F) : #v[x[0], x[1], x[2]] = x := three_eq x
  cases route with
  | hook fd =>
    obtain ⟨_, _, used, _⟩ := effect
    simp [Dispatch.next, routeFlags, DispatchFlags.hook, prior, stamp, updated, finalCursor, WriteStreams.append,
      WriteStreams.ofEvent, previousCount, countDelta, used, threeLimbs, low]
  | _ =>
    simp [Dispatch.next, routeFlags, DispatchFlags.hook, prior, stamp, updated, finalCursor, WriteStreams.append,
      WriteStreams.ofEvent, previousCount, destinationOffset, countDelta, threeLimbs, low]

/-- Each actual WRITE constructs a valid physical dispatch row. The cursor entering the row uses
the last WRITE clock and all preceding stream effects. Its output is the real post-call cursor. -/
theorem native_dispatch_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    ∃ current next length buffer cursor,
      executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current ∧
      executionTrajectory (policy SP1Prime image) image.program source.realize events (cut+1) = some next ∧
      WriteObservations.read? current.sail call = some (length, buffer) ∧
      HintQueue.storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut)
        (HintQueue.ofList source.host.io.hints) = some cursor ∧
      let previous := (events.take cut).foldl advanceWriteClock source.clock
      let row := dispatchRow call.arg1 call.arg2 length current.clock previous
        (WriteStreams.fromEndpoints source.host current.host) current.host cursor.1
      row.Valid ∧ row.next row.flags = finalCursor (current.clock + 1) (WriteStreams.fromEndpoints source.host next.host) := by
  obtain ⟨current, next, length, buffer, read, currentAt, nextAt, effect, _⟩ := groups_of_admissibleExecution run present write
  obtain ⟨a, left, _⟩ := run.1.2.split cut
  obtain ⟨b, toNext, right⟩ := run.1.2.split (cut+1)
  have eqCurrent : a = current := Option.some.inj (left.replay.symm.trans currentAt)
  have eqNext : b = next := Option.some.inj (toNext.replay.symm.trans nextAt)
  subst a b
  obtain ⟨_, cursor, _, _, beforeStore, _⟩ := admissibleExecution_hintInventory run cut
  obtain ⟨_, _, lo, hi, count, _⟩ := WriteObservations.read?_eq_some_iff.mp read
  let route := WriteRoute.ofDescriptor call.arg1
  let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
  let earlier := WriteStreams.fromEndpoints source.host current.host
  let delta := WriteStreams.ofEvent route current.host bytes
  let later := WriteStreams.fromEndpoints next.host target.host
  have size : bytes.length = length.toNat := WriteObservations.payload_length count
  have front : (earlier.append delta).Binds source.host next.host :=
    (execution_streams left).append (WriteStreams.ofEvent_binds effect)
  have full : WriteStreams.fromEndpoints source.host target.host = (earlier.append delta).append later :=
    (front.append (execution_streams right)).unique
  have paid := admissible_streamCost run
  rw [full] at paid
  have covered := counter_le_cost route (earlier.append delta) later
  have inc : previousCount route earlier + countDelta route length.toNat < 2^48 := by
    rw [← size, ← counter_after effect earlier]
    exact covered.trans_lt paid
  have window : destinationOffset route earlier + length.toNat < 2^48 := by
    cases h : route <;> simp only [h, destinationOffset, previousCount, countDelta, Nat.zero_add] at inc ⊢ <;> omega
  have endTime := run.1.2.clock_at present currentAt
  have endBound := run.2.2.2.2.2.1
  change current.clock + 264 ≤ target.clock at endTime
  change target.clock < 2^48 at endBound
  refine ⟨current, next, length, buffer, cursor, currentAt, nextAt, read, beforeStore, ?_, ?_⟩
  · exact dispatchRow_valid _ _ _ _ _ _ _ _ (dispatch_clock_le left source.clock (by rfl)) (by omega) (by omega) hi window inc
  · rw [front.unique]
    apply cursor_next effect earlier _ _ _ rfl rfl
    rw [size]
    rfl

end SP1Clean.WriteEffects
