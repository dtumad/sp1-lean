module

public import SP1Clean.Semantics.Resources.ExecutionResources
public import SP1Clean.Semantics.Host.HostReplay
public import SP1Clean.Semantics.Host.HostReceiptProfile

/-! # Host work and occupancy on installed host execution segments

The installed handlers only consume incoming hint buffers. Their complete ordered contents
determine the padded guest writes. Resource peaks are measured on the original execution
observer, including both boundaries of a nonempty segment.
-/

@[expose] public section

namespace SP1Clean.Semantics.HostReceiptProfile

open Machine Soundness.Target

variable {includeVerify : Bool}
variable {policy : HostPolicy} {program : GuestProgram}
  {source target : ExecutionState} {events : List ExecutionEvent}

private theorem hostFrameSafe {e : ExecutionEvent} (allowed : event includeVerify e) : HostFrameSafe e := by
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
    (allowed : event includeVerify e) :
    ∃ consumed, source.host.io.hints = consumed ++ target.host.io.hints ∧
      source.eventResources policy e .readBytes = 0 ∧ source.eventResources policy e .allocatedHints = 0 ∧
      source.eventResources policy e .writeBytes = (consumed.map fun bytes => (hintWriteBytes bytes).length).sum := by
  cases step with
  | ordinary => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, rfl, _, rfl⟩ := HostState.step_observations success
    have safe : execution.kind ≠ .write := fun eq => ne_write allowed (congrArg SyscallKind.code eq)
    simpa only [ExecutionState.eventResources, HostState.eventResources, ran] using run_cost ran safe

/-- A registered host segment pops exactly an incoming prefix, writes each buffer with its full
mandatory padding, and accumulates zero host guest-read bytes and zero newly allocated hints. -/
theorem queue_work (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event includeVerify e) :
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
    (allowed : ∀ e ∈ events, event includeVerify e) :
    target.host.requests = source.host.requests ∧ target.host.replies = source.host.replies ∧
      target.host.io.publicOutput = source.host.io.publicOutput ∧ target.host.stdout = source.host.stdout ∧
      target.host.stderr = source.host.stderr := by
  have frame := path.host_frame (fun e mem => hostFrameSafe (allowed e mem))
  rw [frame]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Consuming an incoming buffer pays for its mandatory padded write from that buffer's
length-prefixed boundary payload. Empty buffers pay the full eight-byte word as well. -/
theorem writes_add_hostPayload_le (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event includeVerify e) :
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
    (allowed : ∀ e ∈ events, event includeVerify e) (kind : ResourceKind)
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

/-- Nonempty installed host segments attain their host occupancy peaks at entry.
The empty tape has zero event usage; its source occupancy is checked separately. -/
theorem peak (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event includeVerify e) (kind : ResourceKind)
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
    (allowed : ∀ e ∈ events, event includeVerify e) (cut : ℕ) :
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

/-- Charges of a registered host segment under the incoming occupancy and elapsed-tick checks.
The event and write ceilings can be chosen independently in an arbitrary limit record. -/
structure ResourceFacts (limits : ResourceLimits) (source target : ExecutionState)
    (events : List ExecutionEvent) (usage : ResourceUsage) : Prop where
  /-- Number of retired events, including host calls. -/
  count : usage .events = events.length
  /-- Exact elapsed interaction clock. -/
  elapsed : usage .ticks = target.clock - source.clock
  /-- The measured ticks fit the declared ceiling. -/
  ticks : usage .ticks ≤ limits.ticks
  /-- Each retirement costs at least eight ticks. -/
  count_le : events.length ≤ limits.ticks / 8
  /-- The installed handlers issue no guest-buffer reads. -/
  reads : usage .readBytes = 0
  /-- No installed handler creates a fresh hint. -/
  allocations : usage .allocatedHints = 0
  /-- Exact ordered buffers consumed and bytes written, including mandatory padding. -/
  writes : ∃ consumed, source.host.io.hints = consumed ++ target.host.io.hints ∧
    usage .writeBytes = (consumed.map fun bytes => (hintWriteBytes bytes).length).sum
  /-- Every padded write is paid from host data that was present at entry. -/
  paid : usage .writeBytes + target.host.payloadCost ≤ source.host.payloadCost
  /-- The checked incoming boundary includes its full host payload. -/
  payload : source.host.payloadCost ≤ limits.boundaryBytes
  /-- The prefix peaks and the reached state's four host gauges fit their declared ceilings. -/
  occupancy : ∀ kind ∈ [ResourceKind.liveHints, .liveHintBytes, .requests, .outputBytes],
    usage kind ≤ limits.ceiling kind ∧ target.resources kind ≤ limits.ceiling kind

/-- Derive the independent charges from the actual tape, checked source and elapsed ticks. -/
theorem resourceFacts {limits : ResourceLimits} (path : ExecutionPath policy program source events target)
    (allowed : ∀ e ∈ events, event includeVerify e) (incoming : source.resources.Fits limits)
    (ticks : executionResources policy program source events .ticks ≤ limits.ticks) :
    ResourceFacts limits source target events (executionResources policy program source events) := by
  have clock := path.clock
  have count := event_count_le_ticks events
  rw [path.resources_ticks] at ticks
  obtain ⟨consumed, queue, reads, allocations, writes⟩ := queue_work path allowed
  refine ⟨path.resources_events, ?_, path.resources_ticks ▸ ticks, by omega, reads, allocations,
    ⟨consumed, queue, writes⟩, writes_add_hostPayload_le path allowed, ?_, ?_⟩
  · rw [path.resources_ticks]
    omega
  · have bound := incoming .boundaryBytes
    change source.memorySupport.card + source.host.payloadCost + 8 + _ ≤ limits.boundaryBytes at bound
    omega
  · intro kind gauge
    refine ⟨?_, (occupancy_le path allowed kind gauge).trans (incoming kind)⟩
    rw [peak path allowed kind gauge]
    split <;> simp [incoming kind]

variable {limits : ResourceLimits} {usage : ResourceUsage}

/-- After the endpoint and elapsed-tick checks, the two independent work ceilings are exactly
what remains for the nine semantic measures other than peak complete-boundary payload. -/
theorem ResourceFacts.fits_iff (facts : ResourceFacts limits source target events usage) :
    (∀ kind, kind ≠ .boundaryBytes → usage kind ≤ limits.ceiling kind) ↔
      events.length ≤ limits.events ∧ usage .writeBytes ≤ limits.writeBytes := by
  constructor
  · intro fits
    exact ⟨facts.count ▸ fits .events (by decide), fits .writeBytes (by decide)⟩
  · rintro ⟨count, writes⟩ kind checked
    cases kind with
    | events => exact facts.count ▸ count
    | ticks => exact facts.ticks
    | writeBytes => exact writes
    | readBytes => simp [facts.reads]
    | allocatedHints => simp [facts.allocations]
    | liveHints | liveHintBytes | requests | outputBytes => exact (facts.occupancy _ (by simp)).1
    | boundaryBytes => exact (checked rfl).elim

/-- At native limits the elapsed ticks pay for every event and the incoming payload pays for
all padded writes. This includes empty paths. -/
theorem ResourceFacts.native_bounds {characteristic : ℕ}
    (facts : ResourceFacts (ResourceLimits.native characteristic) source target events usage)
    (kind : ResourceKind) (checked : kind ≠ .boundaryBytes) :
    usage kind ≤ (ResourceLimits.native characteristic).ceiling kind ∧
      target.resources kind ≤ (ResourceLimits.native characteristic).ceiling kind := by
  refine ⟨facts.fits_iff.mpr ⟨facts.count_le, ?_⟩ kind checked, ?_⟩
  · exact (Nat.le_add_right _ _).trans (facts.paid.trans facts.payload)
  · cases kind with
    | events | ticks | readBytes | allocatedHints | writeBytes => exact Nat.zero_le _
    | liveHints | liveHintBytes | requests | outputBytes => exact (facts.occupancy _ (by simp)).2
    | boundaryBytes => exact (checked rfl).elim

end SP1Clean.Semantics.HostReceiptProfile
