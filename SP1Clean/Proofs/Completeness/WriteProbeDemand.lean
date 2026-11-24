import SP1Clean.Proofs.Completeness.WriteObservations
import SP1Clean.FormalModel.ShardResources
import ToClean.Air.DemandPadding

/-! # Demand of the released read-only WRITE packets

A packet contains the actual x12 value and the aligned RAM words from the same replay cut.
The existing read-byte charge pays for payload length; a per-call term covers alignment even
for an unaligned empty buffer. Every call consumes the ordinary ECALL clock duration.
-/

namespace SP1Clean.TraceGen.WriteObservations
open Semantics Machine FormalModel.Shard Soundness.Target

/-- A successful observation returns x12 and the complete ordered word slice read by WRITE. -/
abbrev Packet := BitVec 64 × List (BitVec 64)

/-- The released raw syscall code, tested on the complete event label. -/
def isWriteCall : ExecutionEvent → Bool
  | .ordinary => false
  | .syscall call => decide (call.rawCode = SyscallKind.write.code)

/-- Inspect a single event. A successful non-WRITE yields an empty observation, while a
missing required WRITE read rejects the event. -/
def packetAt? (source : SailState) : ExecutionEvent → Option (Option Packet)
  | .ordinary => some none
  | .syscall call =>
    if call.rawCode = SyscallKind.write.code then (read? source call).map some else some none

/-- Collect in tape order, dropping only non-WRITE events. A missing required word rejects
the collection, including when the missing unaligned word supplies zero payload bytes. -/
noncomputable def packets? (host : HostPolicy) (program : GuestProgram) :
    ExecutionState → List ExecutionEvent → Option (List Packet)
  | _, [] => some []
  | current, event :: later => do
    let next ← replayStep? host program current event
    let packet ← packetAt? current.sail event
    let tail ← packets? host program next later
    return packet.toList ++ tail

/-- The collection contains one x12 observation for every WRITE label on the actual tape. -/
theorem packets_length {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {packets : List Packet}
    (collected : packets? host program source events = some packets) :
    packets.length = events.countP isWriteCall := by
  induction events generalizing source packets with
  | nil => cases collected; rfl
  | cons event rest ih =>
    simp only [packets?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at collected
    obtain ⟨_, _, here, got, later, done, rfl⟩ := collected
    have tail := ih done
    cases event with
    | ordinary =>
      cases got
      simpa [List.countP_cons, isWriteCall] using tail
    | syscall call =>
      by_cases code : call.rawCode = SyscallKind.write.code
      · simp only [packetAt?, ite_eq_left code, Option.map_eq_some_iff] at got
        obtain ⟨packet, _, rfl⟩ := got
        simp [isWriteCall, code, tail]
      · simp only [packetAt?, ite_eq_right code, Option.some.injEq] at got
        subst here
        simpa [List.countP_cons, isWriteCall, code] using tail

/-- At each WRITE cut the uniquely ranked packet was read from the actual incoming Sail state. -/
theorem packets_at {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {packets : List Packet}
    (collected : packets? host program source events = some packets) {cut : ℕ} {call : CoreSyscallEvent}
    (present : events[cut]? = some (.syscall call)) (code : call.rawCode = SyscallKind.write.code) :
    ∃ current packet, executionTrajectory host program source events cut = some current ∧
      read? current.sail call = some packet ∧ packets[(events.take cut).countP isWriteCall]? = some packet := by
  induction events generalizing source packets cut with
  | nil => simp at present
  | cons head rest ih =>
    simp only [packets?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at collected
    obtain ⟨next, step, here, got, later, done, rfl⟩ := collected
    cases cut with
    | zero =>
      cases present
      simp only [packetAt?, ite_eq_left code, Option.map_eq_some_iff] at got
      obtain ⟨packet, read, rfl⟩ := got
      exact ⟨source, packet, rfl, read, rfl⟩
    | succ cut =>
      obtain ⟨current, packet, reached, read, rank⟩ := ih done present
      refine ⟨current, packet, by simpa [executionTrajectory, replayEvents?, step] using reached, read, ?_⟩
      cases head with
      | ordinary =>
        cases got
        simpa [List.countP_cons, isWriteCall] using rank
      | syscall earlier =>
        by_cases active : earlier.rawCode = SyscallKind.write.code
        · simp only [packetAt?, ite_eq_left active, Option.map_eq_some_iff] at got
          obtain ⟨first, _, rfl⟩ := got
          simpa [List.countP_cons, isWriteCall, active] using rank
        · simp only [packetAt?, ite_eq_right active, Option.some.injEq] at got
          subst here
          simpa [List.countP_cons, isWriteCall, active] using rank

/-- Number of aligned RAM-word probes, counting observations repeated at distinct cuts. -/
def wordProbes (packets : List Packet) : ℕ := (packets.map (fun packet => packet.2.length)).sum

/-- The requested byte lengths read from x12 at these actual call positions. -/
def requestedBytes (packets : List Packet) : ℕ := (packets.map (fun packet => packet.1.toNat)).sum

/-- Rounding both endpoints adds at most fourteen bytes to the complete aligned footprint. -/
theorem eight_mul_wordCount_le (address length : ℕ) : 8 * wordCount address length ≤ length + 14 := by
  unfold wordCount
  omega

private theorem step_cost {host : HostPolicy} {program : GuestProgram} {current next : ExecutionState}
    {event : ExecutionEvent} {packet : Option Packet} (step : ExecutionStep host program current event next)
    (collected : packetAt? current.sail event = some packet) :
    requestedBytes packet.toList = current.eventResources host event .readBytes ∧
    264 * packet.toList.length ≤ event.duration ∧
    8 * wordProbes packet.toList ≤ requestedBytes packet.toList + 14 * packet.toList.length := by
  cases step with
  | ordinary =>
    cases collected
    exact ⟨rfl, Nat.zero_le _, le_rfl⟩
  | syscall success =>
    obtain ⟨pc, run, _, _, ran, _, _, rfl⟩ := HostState.step_observations success
    by_cases kind : run.kind = .write
    · have code : (run.toEvent current.clock pc).rawCode = SyscallKind.write.code := congrArg SyscallKind.code kind
      simp only [packetAt?, ite_eq_left code, Option.map_eq_some_iff] at collected
      obtain ⟨⟨len, buffer⟩, got, rfl⟩ := collected
      have facts := read?_eq_some_iff.mp got
      have x : (HostReadContext.ofSail current.sail).register 12 = some len := facts.2.1
      have bounds := eight_mul_wordCount_le run.arg2.toNat len.toNat
      have size : buffer.length = wordCount run.arg2.toNat len.toNat := facts.2.2.2.2.1
      have span : run.readSpans? (.ofSail current.sail) = some [⟨run.arg2.toNat, len.toNat⟩] := by
        unfold HostExecution.readSpans?
        rw [kind]
        change ((HostReadContext.ofSail current.sail).register 12).map _ = _
        rw [x]
        rfl
      refine ⟨?_, le_rfl, ?_⟩
      · simp [requestedBytes, ExecutionState.eventResources, HostState.eventResources, ran, HostState.executionResources,
          HostExecution.readByteCount, span]
      · simpa [wordProbes, requestedBytes, size] using bounds
    · have code : (run.toEvent current.clock pc).rawCode ≠ SyscallKind.write.code := fun eq => kind (SyscallKind.code_injective eq)
      simp only [packetAt?, ite_eq_right code, Option.some.injEq] at collected
      subst packet
      have empty : run.readSpans? (HostReadContext.ofSail current.sail) = some [] := by
        cases selected : run.kind <;> simp_all [HostExecution.readSpans?]
      refine ⟨?_, Nat.zero_le _, le_rfl⟩
      simp [requestedBytes, ExecutionState.eventResources, HostState.eventResources, ran, HostState.executionResources,
        HostExecution.readByteCount, empty]

/-- A successful collection on any execution path accounts for exactly its semantic read bytes.
The two upper bounds need no shard preset, source memory bound, or descriptor restriction. -/
theorem packets_cost {host : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath host program source events target)
    {packets : List Packet} (collected : packets? host program source events = some packets) :
    requestedBytes packets = executionResources host program source events .readBytes ∧
    264 * packets.length ≤ (events.map ExecutionEvent.duration).sum ∧
    8 * wordProbes packets ≤ requestedBytes packets + 14 * packets.length := by
  induction path generalizing packets with
  | nil =>
    cases collected
    exact ⟨rfl, le_rfl, le_rfl⟩
  | cons step _ ih =>
    simp only [packets?, step.replay, Option.bind_some, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at collected
    obtain ⟨here, atRow, later, rest, rfl⟩ := collected
    obtain ⟨bytes, time, words⟩ := step_cost step atRow
    obtain ⟨suffixBytes, suffixTime, suffixWords⟩ := ih rest
    have bytes_append : requestedBytes (here.toList ++ later) = requestedBytes here.toList + requestedBytes later := by
      simp [requestedBytes]
    have words_append : wordProbes (here.toList ++ later) = wordProbes here.toList + wordProbes later := by
      simp [wordProbes]
    rw [executionResources_cons step, bytes_append, words_append, List.length_append, List.map_cons, List.sum_cons]
    simp only [ResourceUsage.combine, ResourceKind.cumulative, ↓reduceIte, ExecutionState.resources, Nat.zero_add]
    exact ⟨congrArg₂ (· + ·) bytes suffixBytes, by omega, by omega⟩

private theorem packets_from {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events)
    {current last : ExecutionState} {later : List ExecutionEvent}
    (path : ExecutionPath (policy p image) image.program current later last)
    (before : List ExecutionEvent) (part : events = before ++ later)
    (reached : replayEvents? (policy p image) image.program source.realize before = some current) :
    ∃ packets, packets? (policy p image) image.program current later = some packets := by
  induction path generalizing before with
  | nil => exact ⟨[], rfl⟩
  | @cons current middle last event later step tail ih =>
    have part' : events = (before ++ [event]) ++ later := by simpa only [List.append_assoc, List.singleton_append] using part
    have reached' : replayEvents? (policy p image) image.program source.realize (before ++ [event]) = some middle := by
      simp only [replayEvents?_append, reached, Option.bind_some, replayEvents?, step.replay]
    obtain ⟨rest, collected⟩ := ih _ part' reached'
    cases event with
    | ordinary => exact ⟨rest, by simp [packets?, packetAt?, step.replay, collected]⟩
    | syscall call =>
      by_cases code : call.rawCode = SyscallKind.write.code
      · have present : events[before.length]? = some (.syscall call) := by simp [part]
        have atCut : executionTrajectory (policy p image) image.program source.realize events before.length = some current := by
          simpa [executionTrajectory, part] using reached
        obtain ⟨s, frontier, _, len, buffer, built, _, _, got, _⟩ := of_admissibleExecution execution present code
        obtain ⟨t, f, replay, same, _⟩ := admissibleExecution_mixedAccessPrefix execution before.length
        obtain rfl := Option.some.inj (replay.symm.trans atCut)
        obtain rfl := (Prod.mk.inj (Option.some.inj (built.symm.trans same))).1
        exact ⟨(len, buffer) :: rest, by simp [packets?, packetAt?, code, got, step.replay, collected]⟩
      · exact ⟨rest, by simp [packets?, packetAt?, code, step.replay, collected]⟩

/-- Complete execution semantics supply every required WRITE packet at arbitrary resource limits. -/
theorem admissible_packets {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) :
    ∃ packets, packets? (policy p image) image.program source.realize events = some packets :=
  packets_from execution execution.1.2 [] rfl rfl

/-- The only numeric premises used for the native probe height are the actual tick and read-byte
ceilings. Each packet contributes one x12 probe, including calls which read no RAM words. -/
theorem packets_native_bound {host : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath host program source events target)
    {packets : List Packet} (collected : packets? host program source events = some packets)
    (ticks : (events.map ExecutionEvent.duration).sum ≤ 2 ^ 24)
    (reads : executionResources host program source events .readBytes ≤ 2 ^ 31 - 2 ^ 24) :
    packets.length ≤ 63550 ∧ wordProbes packets ≤ 266449516 ∧
      wordProbes packets + packets.length ≤ 266513066 ∧
      Air.Flat.WitnessGeneration.demandHeight (wordProbes packets + packets.length) ≤ 2 ^ 28 := by
  obtain ⟨bytes, time, words⟩ := packets_cost path collected
  have paid := bytes.le.trans reads
  change requestedBytes packets ≤ 2130706432 at paid
  refine ⟨by omega, by omega, by omega, Air.Flat.WitnessGeneration.demandHeight_le_pow ?_⟩
  omega

end SP1Clean.TraceGen.WriteObservations
