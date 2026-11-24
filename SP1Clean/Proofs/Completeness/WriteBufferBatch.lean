import SP1Clean.Proofs.Completeness.WriteBufferRows
import SP1Clean.Proofs.Completeness.WriteProbeDemand

/-! # Complete read-only WRITE demand at the original tape positions

The existing semantic packet collector owns the reads. We pair it with the WRITE labels
in chronological order, retaining each label's absolute clock, operands, and tape index.
-/

namespace SP1Clean.WriteBuffer

open Semantics Machine FormalModel.Shard TraceGen Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Located native buffer inputs corresponding to one actual WRITE packet. -/
structure PacketRows (F : Type) where
  /-- Position in the chronological guest event tape. -/
  cut : ℕ
  /-- The full authenticated header and its two cursor endpoints. -/
  span : Span F
  /-- Every demanded aligned word, in released read order. -/
  steps : List (Step F)

/-- x12 is read first, followed by all aligned RAM words, at the same original cut. -/
def PacketRows.reads (packet : PacketRows (ZMod p)) : List (WriteProbe.Read (ZMod p)) :=
  ⟨Address.ofNat 12, packet.span.header.clock, packet.span.header.length⟩ :: packet.steps.map Step.read

private def writeLabels (start : ℕ) : List ExecutionEvent → List (ℕ × CoreSyscallEvent)
  | [] => []
  | event :: rest =>
    let tail := writeLabels (start + 1) rest
    match event with
    | .ordinary => tail
    | .syscall call => if call.rawCode = SyscallKind.write.code then (start, call) :: tail else tail

private theorem labels_length (start : ℕ) (events : List ExecutionEvent) :
    (writeLabels start events).length = events.countP WriteObservations.isWriteCall := by
  induction events generalizing start with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | ordinary => simp [writeLabels, WriteObservations.isWriteCall, ih]
    | syscall call =>
      by_cases write : call.rawCode = SyscallKind.write.code <;>
        simp [writeLabels, WriteObservations.isWriteCall, write, ih]

private theorem labels_at (start : ℕ) {events : List ExecutionEvent} {cut : ℕ} {call : CoreSyscallEvent}
    (atCut : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    (writeLabels start events)[(events.take cut).countP WriteObservations.isWriteCall]? = some (start + cut, call) := by
  induction events generalizing start cut with
  | nil => simp at atCut
  | cons event rest ih =>
    cases cut with
    | zero =>
      cases atCut
      simp [writeLabels, write]
    | succ cut =>
      have tail := ih (start + 1) (by simpa using atCut)
      cases event with
      | ordinary => simpa [writeLabels, List.countP_cons, WriteObservations.isWriteCall, Nat.add_assoc, Nat.add_comm 1] using tail
      | syscall earlier =>
        by_cases isWrite : earlier.rawCode = SyscallKind.write.code <;>
          simpa [writeLabels, List.countP_cons, WriteObservations.isWriteCall, isWrite, Nat.add_assoc, Nat.add_comm 1] using tail

/-- Physical rows for an original WRITE label and its actual semantic packet. -/
def makePacketRows (location : ℕ × CoreSyscallEvent) (packet : WriteObservations.Packet) : PacketRows (ZMod p) :=
  let h := headerOfCall (p := p) location.2.clock location.2 packet.1
  ⟨location.1, Span.populate h, wordSteps h.clock (location.2.arg2.toNat / 8) (packet.2.map bitVecToWord)⟩

/-- Pair the original WRITE labels and the existing semantic collector's ordered result. -/
def packetRows (events : List ExecutionEvent) (packets : List WriteObservations.Packet) : List (PacketRows (ZMod p)) :=
  List.zipWith makePacketRows (writeLabels 0 events) packets

private theorem relatedRowsFrom {α : Type} (collect : ExecutionEvent × Nat → Option α)
    (packet : α → WriteObservations.Packet) (related : PacketRows (ZMod p) → α → Prop)
    (events : List ExecutionEvent) (start : Nat)
    (active : ∀ e i, (e,i) ∈ events.zipIdx start → (collect (e,i)).isSome = WriteObservations.isWriteCall e)
    (row : ∀ call i x, (.syscall call,i) ∈ events.zipIdx start → call.rawCode = SyscallKind.write.code →
      collect (.syscall call,i) = some x → related (makePacketRows (i,call) (packet x)) x) :
    let entries := (events.zipIdx start).filterMap collect
    List.Forall₂ related (List.zipWith makePacketRows (writeLabels start events) (entries.map packet)) entries := by
  induction events generalizing start with
  | nil => exact .nil
  | cons event rest ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons] at *
    have tail := ih (start+1) (fun e i m => active e i (.tail _ m)) (fun call i x m => row call i x (.tail _ m))
    have selected := active event start (.head _)
    cases event with
    | ordinary =>
      have none : collect (.ordinary,start) = none := by simpa [WriteObservations.isWriteCall] using selected
      simpa only [none,writeLabels] using tail
    | syscall call =>
      by_cases write : call.rawCode = SyscallKind.write.code
      · have someEntry : (collect (.syscall call,start)).isSome := by simpa [WriteObservations.isWriteCall,write] using selected
        obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp someEntry
        simpa only [hx,writeLabels,ite_eq_left write,List.map_cons,List.zipWith_cons_cons] using
          List.Forall₂.cons (row call start x (.head _) write hx) tail
      · have none : collect (.syscall call,start) = none := by simpa [WriteObservations.isWriteCall,write] using selected
        simpa only [none,writeLabels,ite_eq_right write] using tail

/-- A collector that emits exactly at WRITE cuts is paired with the complete buffer rows in that
same order. The local relation can depend on the original label, its index, and the emitted packet. -/
theorem packetRows_related {α : Type} (collect : ExecutionEvent × Nat → Option α)
    (packet : α → WriteObservations.Packet) (related : PacketRows (ZMod p) → α → Prop)
    (events : List ExecutionEvent)
    (active : ∀ e i, events[i]? = some e → (collect (e,i)).isSome = WriteObservations.isWriteCall e)
    (row : ∀ call i x, events[i]? = some (.syscall call) → call.rawCode = SyscallKind.write.code →
      collect (.syscall call,i) = some x → related (makePacketRows (i,call) (packet x)) x) :
    let entries := events.zipIdx.filterMap collect
    List.Forall₂ related (packetRows events (entries.map packet)) entries :=
  relatedRowsFrom collect packet related events 0 (fun e i m => active e i (List.mk_mem_zipIdx_iff_getElem?.mp m))
    (fun call i x m => row call i x (List.mk_mem_zipIdx_iff_getElem?.mp m))

/-- A successful collection supplies one complete packet at every WRITE position. -/
theorem packetRows_length {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? host program source events = some packets) :
    (packetRows (p := p) events packets).length = events.countP WriteObservations.isWriteCall := by
  simp [packetRows, labels_length, WriteObservations.packets_length collected]

/-- Ordered input to the read-only provider. Each request retains its original execution cut. -/
def readDemand (rows : List (PacketRows (ZMod p))) : List (ℕ × WriteProbe.Read (ZMod p)) :=
  rows.flatMap fun packet => packet.reads.map (packet.cut, ·)

private theorem zip_readDemand_length (labels : List (ℕ × CoreSyscallEvent)) (packets : List WriteObservations.Packet)
    (equal : labels.length = packets.length) :
    (readDemand (p := p) (List.zipWith makePacketRows labels packets)).length =
      WriteObservations.wordProbes packets + packets.length := by
  induction labels generalizing packets with
  | nil =>
    have empty : packets = [] := List.length_eq_zero_iff.mp equal.symm
    simp [empty, readDemand, WriteObservations.wordProbes]
  | cons label rest ih =>
    cases packets with
    | nil => simp at equal
    | cons first later =>
      have tail := ih later (by simpa using equal)
      change (List.map _ (PacketRows.reads (makePacketRows (p := p) label first)) ++
        readDemand (List.zipWith makePacketRows rest later)).length = _
      simp only [List.length_append, List.length_map, tail, PacketRows.reads, List.length_cons,
        makePacketRows, wordSteps, List.length_zipIdx, WriteObservations.wordProbes, List.map_cons, List.sum_cons]
      omega

/-- Exact size of the concrete demand list. It counts x12 even for packets with no RAM words. -/
theorem readDemand_length {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? host program source events = some packets) :
    (readDemand (packetRows (p := p) events packets)).length = WriteObservations.wordProbes packets + packets.length :=
  zip_readDemand_length _ packets ((labels_length _ _).trans (WriteObservations.packets_length collected).symm)

/-- The located request list fits the released native height under the two existing semantic resource ceilings. -/
theorem readDemand_height {host : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (path : ExecutionPath host program source events target)
    (collected : WriteObservations.packets? host program source events = some packets)
    (ticks : (events.map ExecutionEvent.duration).sum ≤ 2 ^ 24)
    (reads : executionResources host program source events .readBytes ≤ 2 ^ 31 - 2 ^ 24) :
    Air.Flat.WitnessGeneration.demandHeight (readDemand (packetRows (p := p) events packets)).length ≤ 2 ^ 28 := by
  rw [readDemand_length collected]
  exact (WriteObservations.packets_native_bound path collected ticks reads).2.2.2

/-- Each packet's index in the batch is the count of preceding WRITEs. The read at
that position came from the actual incoming state and carries its absolute clock. -/
theorem packetRows_at {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (run : AdmissibleExecution limits p image source target events)
    (collected : WriteObservations.packets? (policy p image) image.program source.realize events = some packets)
    {cut : ℕ} {call : CoreSyscallEvent} (atCut : events[cut]? = some (.syscall call))
    (write : call.rawCode = SyscallKind.write.code) :
    ∃ current frontier len buffer,
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      call.clock = current.clock ∧ WriteObservations.read? current.sail call = some (len, buffer) ∧
      (packetRows (p := p) events packets)[(events.take cut).countP WriteObservations.isWriteCall]? =
        some (makePacketRows (cut, call) (len, buffer)) := by
  obtain ⟨before, ⟨length, words⟩, reached, got, rank⟩ := WriteObservations.packets_at collected atCut write
  obtain ⟨current, frontier, next, reached', prefixAt, step, _⟩ := admissibleExecution_syscall_from_prefix run atCut
  obtain rfl := Option.some.inj (reached'.symm.trans reached)
  refine ⟨_, frontier, length, words, prefixAt, ?_, got, ?_⟩
  · cases step with
    | syscall success =>
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := HostState.step_observations success
      rfl
  · simp [packetRows, List.getElem?_zipWith, labels_at 0 atCut write, rank]

private theorem cut_of_rank (events : List ExecutionEvent) (i : ℕ) (inside : i < events.countP WriteObservations.isWriteCall) :
    ∃ cut call, events[cut]? = some (.syscall call) ∧ call.rawCode = SyscallKind.write.code ∧
      (events.take cut).countP WriteObservations.isWriteCall = i := by
  induction events generalizing i with
  | nil => simp at inside
  | cons event rest ih =>
    by_cases yes : WriteObservations.isWriteCall event
    · cases event with
      | ordinary => simp [WriteObservations.isWriteCall] at yes
      | syscall call =>
        have code : call.rawCode = SyscallKind.write.code := by simpa [WriteObservations.isWriteCall] using yes
        cases i with
        | zero => exact ⟨0, call, rfl, code, rfl⟩
        | succ i =>
          obtain ⟨cut, later, here, write, rank⟩ := ih i (by simpa [List.countP_cons, yes] using inside)
          exact ⟨cut + 1, later, by simpa using here, write, by simp [yes, rank]⟩
    · obtain ⟨cut, later, here, write, rank⟩ := ih i (by simpa [List.countP_cons, yes] using inside)
      exact ⟨cut + 1, later, by simpa using here, write, by simp [yes, rank]⟩

/-- Each packet in the ordered batch comes from one real WRITE and its native memory read. -/
theorem packetRows_member {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet} (run : AdmissibleExecution limits p image source target events)
    (collected : WriteObservations.packets? (policy p image) image.program source.realize events = some packets)
    {row : PacketRows (ZMod p)} (member : row ∈ packetRows events packets) :
    ∃ cut call current frontier len buffer, events[cut]? = some (.syscall call) ∧ call.rawCode = SyscallKind.write.code ∧
      mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      call.clock = current.clock ∧ WriteObservations.read? current.sail call = some (len, buffer) ∧
      row = makePacketRows (cut, call) (len, buffer) := by
  obtain ⟨i, inside, index⟩ := List.mem_iff_getElem.mp member
  obtain ⟨cut, call, present, write, rank⟩ := cut_of_rank events i ((packetRows_length (p := p) collected) ▸ inside)
  obtain ⟨current, frontier, len, buffer, prefixAt, clock, read, located⟩ := packetRows_at run collected present write
  rw [rank, List.getElem?_eq_getElem inside, index] at located
  exact ⟨cut, call, current, frontier, len, buffer, present, write, prefixAt, clock, read, Option.some.inj located⟩

omit [Fact p.Prime] in
/-- Read requests count one x12 length per packet in addition to every concrete aligned word. -/
theorem readDemand_size (rows : List (PacketRows (ZMod p))) :
    (readDemand rows).length = rows.length + (rows.flatMap PacketRows.steps).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [readDemand, List.flatMap_cons, List.length_cons, List.length_append, List.length_map, PacketRows.reads] at ih ⊢
    omega

/-- The physical step inventory includes exactly the word reads of the semantic packet batch. -/
theorem packetRows_words {host : HostPolicy} {program : GuestProgram} {source : ExecutionState}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? host program source events = some packets) :
    ((packetRows (p := p) events packets).flatMap PacketRows.steps).length = WriteObservations.wordProbes packets := by
  have demand := readDemand_length (p := p) collected
  rw [readDemand_size, packetRows_length collected, ← WriteObservations.packets_length collected] at demand
  omega

/-- A read-only supplier can attribute every input to its genuine original cut, architectural
location, and full held Sail word. This includes repeated keys and the extra words of unaligned slices. -/
theorem readDemand_at [Fact (2 ^ 17 < p)] {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (run : AdmissibleExecution limits p image source target events)
    (collected : WriteObservations.packets? (policy p image) image.program source.realize events = some packets)
    {cut : ℕ} {r : WriteProbe.Read (ZMod p)} (member : (cut, r) ∈ readDemand (packetRows events packets)) :
    ∃ current frontier loc, mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
      WriteProbe.ValidKey loc.busAddress ∧ r.key = Address.ofNat loc.busAddress ∧ r.clock = Address.ofNat current.clock ∧
      r.value.isU64 ∧ locContent current.sail loc = some r.value.toBitVec64 := by
  obtain ⟨row, inBatch, tagged⟩ := List.mem_flatMap.mp member
  obtain ⟨actual, actualRead, same⟩ := List.mem_map.mp tagged
  obtain ⟨n, call, current, frontier, len, buffer, _, _, prefixAt, clock, read, rfl⟩ :=
    packetRows_member run collected inBatch
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain ⟨_, x12, lower, upper, count, atWord⟩ := WriteObservations.read?_eq_some_iff.mp read
  let h := headerOfCall (p := p) call.clock call len
  let words := wordSteps h.clock (call.arg2.toNat / 8) (buffer.map bitVecToWord)
  change actual ∈ WriteProbe.Read.mk (Address.ofNat 12) h.clock h.length :: words.map Step.read at actualRead
  rcases List.mem_cons.mp actualRead with rfl | memory
  · exact ⟨current, frontier, .reg 12, prefixAt, Or.inl rfl, rfl, congrArg Address.ofNat clock,
      isU64_bitVecToWord _, by simpa [h, headerOfCall, locContent, toBitVec64_bitVecToWord] using x12⟩
  · obtain ⟨j, inWords, keyAt⟩ := List.mem_iff_getElem.mp memory
    have bj : j < buffer.length := by simpa [words, wordSteps] using inWords
    have wordAt := (rows_of_read (p := p) read call.clock).2.2.2 j
    have wj : j < words.length := by simpa using inWords
    change (words[j]?).map Step.read = _ at wordAt
    simp only [List.getElem?_eq_getElem wj, List.getElem?_eq_getElem bj, Option.map_some, Option.some.injEq] at wordAt
    simp only [List.getElem_map, wordAt] at keyAt
    subst actual
    let loc := MemLoc.ram (WriteObservations.cell call.arg2.toNat j)
    have fits : call.arg2.toNat / 8 + j < 2 ^ 45 := by
      rw [count, WriteObservations.wordCount] at bj
      omega
    have key : loc.busAddress = 8 * (call.arg2.toNat / 8 + j) := by
      simp only [loc, MemLoc.busAddress, WriteObservations.cell, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show call.arg2.toNat / 8 + j < 2 ^ 61 by omega), Nat.mul_comm]
    refine ⟨current, frontier, loc, prefixAt, Or.inr ⟨?_, ?_, ?_⟩, by rw [key], congrArg Address.ofNat clock,
      isU64_bitVecToWord _, ?_⟩
    · rw [key]; omega
    · rw [key]; omega
    · simp [key]
    · simpa [loc, locContent, List.getElem?_eq_getElem bj, toBitVec64_bitVecToWord] using atWord j bj

/-- A complete admissible tape supplies the located read demand for every WRITE.
The same batch serves every cut and its cardinality excludes extra packets. -/
theorem packetRows_of_admissibleExecution {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits p image source target events) :
    ∃ packets, WriteObservations.packets? (policy p image) image.program source.realize events = some packets ∧
      (packetRows (p := p) events packets).length = events.countP WriteObservations.isWriteCall ∧
      ∀ cut call, events[cut]? = some (.syscall call) → call.rawCode = SyscallKind.write.code →
        ∃ current frontier len buffer,
          mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier) ∧
          call.clock = current.clock ∧ WriteObservations.read? current.sail call = some (len, buffer) ∧
          (packetRows (p := p) events packets)[(events.take cut).countP WriteObservations.isWriteCall]? =
            some (makePacketRows (cut, call) (len, buffer)) := by
  obtain ⟨packets, collected⟩ := WriteObservations.admissible_packets run
  exact ⟨packets, collected, packetRows_length collected, fun _ _ event active => packetRows_at run collected event active⟩

end SP1Clean.WriteBuffer
