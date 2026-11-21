module

public import SP1Clean.Semantics.Resources.ExecutionResources
public import SP1Clean.Semantics.Host.HostReplay
public import SP1Clean.Semantics.Host.SixCallProfile

/-! # Host work and occupancy on six-call execution segments

The installed handlers only consume incoming hint buffers. Their complete ordered contents
determine the padded guest writes. Resource peaks are measured on the original execution
observer, including both boundaries of a nonempty segment.
-/

@[expose] public section

namespace SP1Clean.Semantics.SixCallProfile

open Machine Soundness.Target

variable {policy : HostPolicy} {program : GuestProgram}
  {source target : ExecutionState} {events : List ExecutionEvent}

private theorem hostFrameSafe {e : ExecutionEvent} (allowed : event e) : HostFrameSafe e := by
  cases e with
  | ordinary => trivial
  | syscall call => exact ne_write allowed

private theorem run_cost {host : HostState} {context : HostReadContext} {execution : HostExecution}
    (ran : host.run policy context = some execution) (safe : execution.kind ≠ .write) :
    ∃ consumed, host.io.hints = consumed ++ execution.effect.state.io.hints ∧
      host.executionResources context execution .readBytes = 0 ∧
      host.executionResources context execution .allocatedHints = 0 ∧
      host.executionResources context execution .writeBytes =
        (consumed.map fun bytes => (hintWriteBytes bytes).length).sum := by
  have effect := ((host.run_eq_some_iff policy context execution).mp ran).2.2.2.2.2
  cases kind : execution.kind with
  | write => exact (safe kind).elim
  | hintRead =>
    rw [kind] at effect
    obtain ⟨bytes, rest, hints, _, _, _, eq⟩ := (host.execute_hintRead_iff ..).mp effect
    refine ⟨[bytes], ?_⟩
    simp [HostState.executionResources, HostExecution.readByteCount, HostExecution.readSpans?,
      HostState.hintEvent, HintQueue.Event.allocations, HostExecution.writeByteCount,
      HostExecution.writeSpans, kind, eq, hints]
  | enterUnconstrained | hintLength | verifyProof | halt | commit | commitDeferred =>
    rw [kind] at effect
    simp only [HostState.executeKind] at effect
    try split_ifs at effect
    all_goals
      obtain eq := (Option.some.inj effect).symm
      exact ⟨[], by simp [HostState.executionResources, HostExecution.readByteCount, HostExecution.readSpans?,
        HostState.hintEvent, HintQueue.Event.allocations, HostExecution.writeByteCount,
        HostExecution.writeSpans, eq, kind]⟩

private theorem step_cost {e : ExecutionEvent} (step : ExecutionStep policy program source e target)
    (allowed : event e) :
    ∃ consumed, source.host.io.hints = consumed ++ target.host.io.hints ∧
      source.eventResources policy e .readBytes = 0 ∧ source.eventResources policy e .allocatedHints = 0 ∧
      source.eventResources policy e .writeBytes = (consumed.map fun bytes => (hintWriteBytes bytes).length).sum := by
  cases step with
  | ordinary => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, rfl, _, rfl⟩ := HostState.step_observations success
    have safe : execution.kind ≠ .write := fun eq => ne_write allowed (congrArg SyscallKind.code eq)
    simpa only [ExecutionState.eventResources, HostState.eventResources, ran] using run_cost ran safe

/-- A six-handler segment pops exactly an incoming prefix, writes each buffer with its full
mandatory padding, and accumulates zero host guest-read bytes and zero newly allocated hints. -/
theorem queue_work (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) :
    ∃ consumed, source.host.io.hints = consumed ++ target.host.io.hints ∧
      executionResources policy program source events .readBytes = 0 ∧
      executionResources policy program source events .allocatedHints = 0 ∧
      executionResources policy program source events .writeBytes =
        (consumed.map fun bytes => (hintWriteBytes bytes).length).sum := by
  induction path with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | @cons before middle after e rest step _ ih =>
    obtain ⟨first, head, read, allocated, written⟩ := step_cost step (allowed _ (List.mem_cons_self ..))
    obtain ⟨later, tail, reads, allocations, writes⟩ := ih (fun e mem => allowed e (List.mem_cons_of_mem _ mem))
    refine ⟨first ++ later, by rw [head, tail, List.append_assoc], ?_⟩
    rw [executionResources_cons step]
    simp [ResourceUsage.combine, ResourceKind.cumulative, ExecutionState.resources,
      read, allocated, written, reads, allocations, writes]

/-- The ordered hook requests and replies and the three output streams are unchanged. -/
theorem streams (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) :
    target.host.requests = source.host.requests ∧ target.host.replies = source.host.replies ∧
      target.host.io.publicOutput = source.host.io.publicOutput ∧ target.host.stdout = source.host.stdout ∧
      target.host.stderr = source.host.stderr := by
  have frame := path.host_frame (fun e mem => hostFrameSafe (allowed e mem))
  rw [frame]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Consuming an incoming buffer pays for its mandatory padded write from that buffer's
length-prefixed boundary payload. Empty buffers pay the full eight-byte word as well. -/
theorem writes_add_hostPayload_le (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) :
    executionResources policy program source events .writeBytes + target.host.payloadCost ≤ source.host.payloadCost := by
  obtain ⟨consumed, queue, _, _, writes⟩ := queue_work path allowed
  obtain ⟨requests, replies, publicOutput, stdout, stderr⟩ := streams path allowed
  have paid : (consumed.map fun bytes => (hintWriteBytes bytes).length).sum ≤
      (consumed.map bytePayloadCost).sum := by
    clear queue writes
    induction consumed with
    | nil => rfl
    | cons bytes rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (by rw [hintWriteBytes_length]; unfold bytePayloadCost; omega) ih
  simp only [writes, HostState.payloadCost, hintPayloadCost, queue, List.map_append,
    List.sum_append, replies, requests, publicOutput, stdout, stderr]
  omega

/-- All four host occupancy observations at any later boundary are bounded by the incoming state. -/
theorem occupancy_le (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) (kind : ResourceKind)
    (hostKind : kind ∈ [.liveHints, .liveHintBytes, .requests, .outputBytes]) :
    target.resources kind ≤ source.resources kind := by
  obtain ⟨consumed, hints, _⟩ := queue_work path allowed
  obtain ⟨requests, _, publicOutput, stdout, stderr⟩ := streams path allowed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hostKind
  rcases hostKind with rfl | rfl | rfl | rfl <;>
    simp [ExecutionState.resources, hints, requests, publicOutput, stdout, stderr]

private theorem event_occupancy (before : ExecutionState) (e : ExecutionEvent) (kind : ResourceKind)
    (hostKind : kind ∈ [.liveHints, .liveHintBytes, .requests, .outputBytes]) :
    before.eventResources policy e kind = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hostKind
  rcases hostKind with rfl | rfl | rfl | rfl <;> cases e <;>
    simp only [ExecutionState.eventResources, HostState.eventResources]
  all_goals split <;> rfl

/-- Nonempty six-handler segments attain their host occupancy peaks at entry.
The empty tape has zero event usage; its source occupancy is checked separately. -/
theorem peak (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) (kind : ResourceKind)
    (hostKind : kind ∈ [.liveHints, .liveHintBytes, .requests, .outputBytes]) :
    executionResources policy program source events kind = if events.isEmpty then 0 else source.resources kind := by
  induction path with
  | nil => rfl
  | @cons before middle after e rest step _ ih =>
    have head := allowed _ (List.mem_cons_self ..)
    have monotone := occupancy_le (ExecutionPath.cons step (.nil middle))
      (by simpa only [List.mem_singleton, forall_eq] using head) kind hostKind
    have tail := ih (fun e mem => allowed e (List.mem_cons_of_mem _ mem))
    have gauge : kind.cumulative = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hostKind
      rcases hostKind with rfl | rfl | rfl | rfl <;> rfl
    rw [executionResources_cons step]
    simp only [ResourceUsage.combine, gauge, Bool.false_eq_true, ↓reduceIte,
      event_occupancy before e kind hostKind, Nat.max_zero, tail, List.isEmpty_cons]
    split <;> omega

/-- At every authenticated cut, the host occupancy peaks of the prefix and the actual
intermediate state's live occupancy satisfy the same incoming ceilings. -/
theorem prefix_host_bounds (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event e) (cut : ℕ) :
    ∃ middle, ExecutionPath policy program source (events.take cut) middle ∧
      ExecutionPath policy program middle (events.drop cut) target ∧
      ∀ kind ∈ [ResourceKind.liveHints, .liveHintBytes, .requests, .outputBytes],
        executionResources policy program source (events.take cut) kind ≤ source.resources kind ∧
        middle.resources kind ≤ source.resources kind := by
  obtain ⟨middle, left, right⟩ := path.split cut
  have admitted := fun e mem => allowed e ((List.take_sublist cut events).subset mem)
  refine ⟨middle, left, right, ?_⟩
  intro kind included
  refine ⟨?_, occupancy_le left admitted kind included⟩
  rw [peak left admitted kind included]
  split <;> omega

end SP1Clean.Semantics.SixCallProfile
