import SP1Clean.Proofs.Completeness.HintInventory
import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Semantics.Execution.ExecutionAccess

/-! # Constructing the HINT_READ word transfers

Each successful read consumes the current persistent node, including its final padded word.
The private word cursor and the Memory payload share the same address and value. The displaced
timestamp comes from the incoming Memory frontier, and the displaced word comes from Sail RAM.
-/

namespace SP1Clean.TraceGen.HintReadTransfers

open Semantics Machine FormalModel.Shard HintQueue Soundness.Target
open HintReadWordChip (RowInput)

private abbrev F := ZMod SP1Prime

/-- The data common to the next-word and last-word rows of one host operation. -/
structure Request where
  /-- Timestamp of the executing ECALL. -/
  clock : ℕ
  /-- Pointer to the popped immutable hint node. -/
  pointer : ℕ
  /-- First destination byte in guest RAM. -/
  address : ℕ
  /-- Complete contents of the popped node, before padding. -/
  bytes : Bytes

/-- Aligned guest byte address of one transfer. -/
def Request.destination (request : Request) (index : ℕ) : ℕ := request.address + index * 8

/-- Select the last-word consumer at the unique final index. -/
def Request.last (request : Request) (index : ℕ) : Bool := decide (index + 1 = wordCount request.bytes)

/-- Prior Memory message with the actual cell address, prior timestamp and overwritten value. -/
private def previous (time address : ℕ) (word : BitVec 64) : Channels.MemoryMsg F :=
  let key := Address.ofNat (p := SP1Prime) address
  ⟨(time / 2 ^ 24 : ℕ), (time % 2 ^ 24 : ℕ), key[0], key[1], key[2], bitVecToWord word⟩

/-- Populate the active physical consumer, including both sides of its RAM transfer. -/
def Request.wordRow (request : Request) (index time : ℕ) (old : BitVec 64) : RowInput F :=
  let cpu := cpuStateCols (p := SP1Prime) request.clock 0
  let address := request.destination index
  let ram := HostRamAccessChip.populate (previous time address old) cpu.clk_high cpu.clk_0_16
    cpu.clk_16_24 (bitVecToWord (wordValue request.bytes index))
  HintReadWordChip.populate (request.last index) ram (Address.ofNat request.pointer) (Address.ofNat index)

/-- The canonical Memory-bus location displaced by this transfer. -/
def Request.cell (request : Request) (index : ℕ) : RamCell :=
  ramCellOfByteAddress (BitVec.ofNat 64 (request.destination index))

/-- All rows in call order. The final zero-padded transfer is present even for an empty node. -/
def Request.rows (request : Request) (frontier : AccessFrontier) (sail : SailState) : List (Bool × RowInput F) :=
  (List.range (wordCount request.bytes)).map fun index =>
    let address := BitVec.ofNat 64 (request.destination index)
    (request.last index, request.wordRow index (frontier (.ram (request.cell index))) ((ramWord64? sail address).getD 0))

theorem Request.rows_length (request : Request) (frontier : AccessFrontier) (sail : SailState) :
    (request.rows frontier sail).length = wordCount request.bytes := by simp [rows]

/-- Decoding the actual installed row payloads gives the ordered semantic padded writes. -/
theorem Request.writes (request : Request) (frontier : AccessFrontier) (sail : SailState)
    (span : HintReadSpan.Domain request.address request.bytes.length) :
    ((request.rows frontier sail).map fun entry =>
      (Address.toNat entry.2.1.address, Word.toBitVec64 entry.2.1.ram.new_value)) =
      wordWrites request.address request.bytes := by
  simp only [rows, List.map_map, wordWrites]
  apply List.map_congr_left
  intro index member
  have pos := List.mem_range.mp member
  have limit := span.bounds.2.2.1
  unfold wordCount at pos
  have fits : request.destination index < 2 ^ 48 := by unfold destination; omega
  change (Address.toNat (Address.ofNat (p := SP1Prime) (request.destination index)),
    Word.toBitVec64 (bitVecToWord (p := SP1Prime) (wordValue request.bytes index))) = _
  rw [Address.toNat_ofNat _ fits, toBitVec64_bitVecToWord]
  rfl

/-- Each row selects the physical next-word table until the sole terminal padding row. -/
theorem Request.markers (request : Request) (frontier : AccessFrontier) (sail : SailState) :
    (request.rows frontier sail).map Prod.fst =
      List.replicate (request.bytes.length / 8) false ++ [true] := by
  simp only [rows, List.map_map, wordCount, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i hi _
      have pos : i < request.bytes.length / 8 := by simpa using hi
      simp [last, wordCount, Nat.ne_of_lt pos]
  · simp [last, wordCount]

/-- A private continuing cursor is literally the next physical row's input cursor. -/
theorem Request.link (request : Request) (index firstTime nextTime : ℕ) (old new : BitVec 64)
    (span : HintReadSpan.Domain request.address request.bytes.length)
    (continues : index + 1 < wordCount request.bytes) :
    (request.wordRow index firstTime old).1.next = (request.wordRow (index + 1) nextTime new).1.previous := by
  have top := span.bounds.2.2
  have last : request.last index = false := by simp [Request.last, Nat.ne_of_lt continues]
  unfold wordCount at continues
  have indexFits : index < 2 ^ 48 := by omega
  have fits : request.destination index < 2 ^ 48 := by unfold destination; omega
  change HintReadWordChip.State.mk _ _ _ (Address.ofNat (Address.toNat (Address.ofNat index) + 1))
    (if request.last index then _ else Address.ofNat (Address.toNat (Address.ofNat (request.destination index)) + 8)) =
    HintReadWordChip.State.mk _ _ _ (Address.ofNat (index + 1)) (Address.ofNat (request.destination (index + 1)))
  rw [last, Address.toNat_ofNat _ indexFits, Address.toNat_ofNat _ fits]
  simp [destination, Nat.add_mul, Nat.add_assoc]
  exact ⟨rfl, rfl, rfl⟩

/-- The two ends of the generated chain coincide with the exact cursor messages installed in
the HINT_READ handler. The previous queue clock affects neither word endpoint. -/
theorem handler_endpoints (store : Store) (head previousClock clock : ℕ) (exec : HostExecution)
    (bytes : Bytes) (length : bytes.length = exec.arg2.toNat)
    (span : HintReadSpan.Domain exec.arg1.toNat bytes.length)
    (firstTime finalTime : ℕ) (firstOld finalOld : BitVec 64) :
    let request : Request := ⟨clock, head, exec.arg1.toNat, bytes⟩
    let handler := HostHintReadChip.populate (p := SP1Prime) store head previousClock clock exec
    (request.wordRow 0 firstTime firstOld).1.previous = handler.first ∧
      (request.wordRow (bytes.length / 8) finalTime finalOld).1.next = handler.final := by
  let cpu := cpuStateCols (p := SP1Prime) clock 0
  have high : cpu.clk_high = ((clock / 2 ^ 24 : ℕ) : F) := by
    rw [show cpu.clk_high = _ from cpuStateCols_clk_high clock 0, Nat.shiftRight_eq_div_pow]
  have low := clkLow_eq (p := SP1Prime) clock 0
  have natural : Word.toNat (bitVecToWord (p := SP1Prime) exec.arg2) = bytes.length := by
    rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord, length]
  have start := Address.toNat_ofNat (p := SP1Prime) exec.arg1.toNat span.bounds.1
  have indexBound : bytes.length / 8 < 2 ^ 48 := by have := span.bounds.2.2.2; omega
  constructor
  · change HintReadWordChip.State.mk cpu.clk_high _ _ _ _ = HintReadWordChip.State.mk _ _ _ _ _
    rw [high]
    change HintReadWordChip.State.mk _ ((cpuStateCols (p := SP1Prime) clock 0).clk_0_16 +
      (cpuStateCols (p := SP1Prime) clock 0).clk_16_24 * 65536) _ _ _ = _
    rw [low]
    change HintReadWordChip.State.mk _ _ (Address.ofNat head) (Address.ofNat 0)
      (Address.ofNat (exec.arg1.toNat + 0 * 8)) = _
    rw [Nat.zero_mul, Nat.add_zero]
    rfl
  · let i := bytes.length / 8
    have last : (Request.mk clock head exec.arg1.toNat bytes).last i = true := by simp [Request.last, wordCount, i]
    change HintReadWordChip.State.mk cpu.clk_high
      ((cpuStateCols (p := SP1Prime) clock 0).clk_0_16 + (cpuStateCols (p := SP1Prime) clock 0).clk_16_24 * 65536)
      (Address.ofNat head) (Address.ofNat (Address.toNat (Address.ofNat i) + 1))
      (if (Request.mk clock head exec.arg1.toNat bytes).last i then Address.ofNat (exec.arg1.toNat + i * 8) else _) =
      HintReadWordChip.State.mk _ _ (Address.ofNat head)
        (Address.ofNat (Word.toNat (bitVecToWord (p := SP1Prime) exec.arg2) / 8 + 1))
        (Address.ofNat (Address.toNat (Address.ofNat exec.arg1.toNat) +
          Word.toNat (bitVecToWord (p := SP1Prime) exec.arg2) / 8 * 8))
    rw [high, low, last, Address.toNat_ofNat i indexBound, start, natural]
    rfl

private theorem val_small {n : ℕ} (small : n < 2 ^ 24) : (n : F).val = n :=
  ZMod.val_natCast_of_lt (small.trans pow24_lt_sp1Prime)

private theorem previous_time {time : ℕ} (fits : time < 2 ^ 48) (address : ℕ) (word : BitVec 64) :
    Semantics.MemoryMsg.timeNat (previous time address word) = time := by
  change ((time / 2 ^ 24 : ℕ) : F).val * 2 ^ 24 + ((time % 2 ^ 24 : ℕ) : F).val = time
  rw [val_small (by omega), val_small (Nat.mod_lt _ (by decide))]
  omega

private theorem clock_time {clock : ℕ} (fits : clock < 2 ^ 48) (phase : clock % 8 = 1) :
    let cpu := cpuStateCols (p := SP1Prime) clock 0
    clkNat cpu.clk_high (cpu.clk_0_16 + cpu.clk_16_24 * 65536 + 1) = clock + 1 := by
  have low := clk_window_of_mod phase
  change _ * 2 ^ 24 + _ = _
  rw [show (1 : F) = ((1 : ℕ) : F) by rfl, clkTarget_eq, cpuStateCols_clk_high,
    Nat.shiftRight_eq_div_pow, val_small (by omega), val_small (by omega)]
  omega

private theorem Request.ram_domain (request : Request) {index time : ℕ} (old : BitVec 64)
    (span : HintReadSpan.Domain request.address request.bytes.length)
    (pos : index < wordCount request.bytes) (fits : request.clock < 2 ^ 48)
    (phase : request.clock % 8 = 1) (earlier : time < request.clock + 1) :
    let cpu := cpuStateCols (p := SP1Prime) request.clock 0
    HostRamAccessChip.Domain (previous time (request.destination index) old) cpu.clk_high cpu.clk_0_16
      cpu.clk_16_24 (bitVecToWord (wordValue request.bytes index)) := by
  have addrBound : request.destination index < 2 ^ 48 := by
    have upper := span.bounds.2.2.1
    unfold destination wordCount at *
    omega
  have addrFacts := Address.bounded_ofNat (p := SP1Prime) (request.destination index)
  have addrRead := Address.toNat_ofNat (p := SP1Prime) (request.destination index) addrBound
  have clk := cpuState_spec (p := SP1Prime) request.clock 0 phase (Address.ofNat 0) 0 1 rfl
  refine ⟨?_, isU64_bitVecToWord _, isU64_bitVecToWord _, ?_, ?_, ?_, clk.1, clk.2, ?_⟩
  · change Word.isU64 (Address.asWord (Address.ofNat (p := SP1Prime) (request.destination index))) ∧ _
    refine ⟨Address.isU64_asWord addrFacts, ?_⟩
    change 2 ^ 16 ≤ Word.toNat (Address.asWord (Address.ofNat (p := SP1Prime) (request.destination index))) ∧
      Word.toNat (Address.asWord (Address.ofNat (p := SP1Prime) (request.destination index))) < 2 ^ 48 ∧
      Word.toNat (Address.asWord (Address.ofNat (p := SP1Prime) (request.destination index))) % 8 = 0
    rw [Address.toNat_asWord, addrRead]
    exact ⟨span.1.trans (Nat.le_add_right _ _), addrBound, by have := span.2.1; unfold destination; omega⟩
  · change ((time / 2 ^ 24 : ℕ) : F).val < 2 ^ 24
    rw [val_small (by omega)]; omega
  · change ((time % 2 ^ 24 : ℕ) : F).val < 2 ^ 24
    rw [val_small (Nat.mod_lt _ (by decide))]
    exact Nat.mod_lt _ (by decide)
  · rw [cpuStateCols_clk_high, Nat.shiftRight_eq_div_pow, val_small (by omega)]
    omega
  · rw [previous_time (by omega), clock_time fits phase]
    exact earlier

/-- A bounded incoming Memory frontier supplies the only chronology input to each installed
consumer. All internal gap, cursor and word columns are constructed by the production circuits. -/
theorem Request.wordRow_assumptions (request : Request) {index time : ℕ} (old : BitVec 64)
    (span : HintReadSpan.Domain request.address request.bytes.length)
    (pos : index < wordCount request.bytes) (pointer : 0 < request.pointer ∧ request.pointer < 2 ^ 48)
    (fits : request.clock < 2 ^ 48) (phase : request.clock % 8 = 1) (earlier : time < request.clock + 1)
    (data : ProverData F) (hint : ProverHint F) :
    (HintReadWordChip.circuit (request.last index)).ProverAssumptions (request.wordRow index time old) data hint := by
  have bound := span.bounds.2.2
  have indexFits : index < 2 ^ 48 := by unfold wordCount at pos; omega
  have addressFits : request.destination index < 2 ^ 48 := by unfold destination wordCount at *; omega
  refine HintReadWordChip.populate_assumptions _ _ _ _ (HostRamAccessChip.populate_assumptions _ _ _ _ _
    (request.ram_domain old span pos fits phase earlier)) (Address.bounded_ofNat _) ?_ (Address.bounded_ofNat _) ?_ ?_ data hint
  · rw [Address.toNat_ofNat _ pointer.2]; exact pointer.1
  · rw [Address.toNat_ofNat _ indexFits]; unfold wordCount at pos; omega
  · intro continuing
    have notLast : index + 1 ≠ wordCount request.bytes := by simpa [last] using continuing
    change Address.toNat (Address.ofNat (p := SP1Prime) (request.destination index)) + 8 < 2 ^ 48
    rw [Address.toNat_ofNat _ addressFits]
    unfold destination wordCount at *
    omega

private theorem Request.window (request : Request) {index : ℕ}
    (span : HintReadSpan.Domain request.address request.bytes.length) (pos : index < wordCount request.bytes) :
    request.destination index + 8 ≤ 2 ^ 48 := by
  have upper := span.2.2
  unfold destination wordCount at *
  omega

private theorem Request.cell_mem (request : Request) {index : ℕ}
    (span : HintReadSpan.Domain request.address request.bytes.length) (pos : index < wordCount request.bytes) :
    (request.cell index).toNat ∈ (MemorySpan.mk request.address (hintWriteBytes request.bytes).length).cells := by
  have window := request.window span pos
  have addrFits : request.destination index < 2 ^ 64 := by omega
  have cellFits : request.destination index / 8 < 2 ^ 61 := by omega
  simp only [cell, ramCellOfByteAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addrFits, Nat.mod_eq_of_lt cellFits]
  exact MemorySpan.byte_cell_mem _ (index * 8) (by
    change index * 8 < (hintWriteBytes request.bytes).length
    rw [wordCount_length]
    omega)

private theorem Request.readback (request : Request) {index : ℕ}
    (span : HintReadSpan.Domain request.address request.bytes.length) (pos : index < wordCount request.bytes)
    (current : SailState) (exec : HostExecution) (pc : BitVec 64)
    (write : exec.effect.write = some ⟨request.address, hintWriteBytes request.bytes⟩) :
    ramWord64? (exec.apply current pc) (BitVec.ofNat 64 (request.destination index)) =
      some (wordValue request.bytes index) := by
  let memory := (default : ByteMemory).writeBytes request.address (hintWriteBytes request.bytes)
  have window := request.window span pos
  have addrFits : request.destination index < 2 ^ 64 := by omega
  have decoded : (BitVec.ofNat 64 (request.destination index)).toNat = request.destination index :=
    Nat.mod_eq_of_lt addrFits
  have observed (slot : Fin 8) :
      (exec.apply current pc).mem.get? ((BitVec.ofNat 64 (request.destination index)).toNat + slot.val) =
        some (memory.read ((BitVec.ofNat 64 (request.destination index)).toNat + slot.val)) := by
    have inside := word_position_bound request.bytes pos slot
    rw [decoded]
    simp only [destination, Nat.add_assoc, memory, ByteMemory.read_writeBytes_inside _ _ _ _ inside]
    change (exec.effect.applyMemory current.mem).get? (request.address + (index * 8 + slot.val)) = _
    simp only [HostEffect.applyMemory, write]
    exact HostMemoryWrite.read_written ⟨request.address, hintWriteBytes request.bytes⟩ current.mem _ inside
  have observedWord := ByteMemory.ramWord64?_of_bytes memory (exec.apply current pc)
    (BitVec.ofNat 64 (request.destination index)) observed
  rw [decoded] at observedWord
  exact observedWord.trans (congrArg some (readWord_writeHint default request.address request.bytes pos))

/-- Authenticity and physical completeness for one occurrence of a word in the constructed batch.
Both Memory records decode to the actual Sail words at the two ends of this host step. -/
def Request.WordAt (request : Request) (index : ℕ) (frontier after : AccessFrontier)
    (source target : SailState) (store : Store) : Prop :=
  let address := BitVec.ofNat 64 (request.destination index)
  let predecessor := frontier (.ram (request.cell index))
  let row := request.wordRow index predecessor ((ramWord64? source address).getD 0)
  (request.rows frontier source)[index]? = some (request.last index, row) ∧ row.2 = 1 ∧
    (row.1.step (request.last index)).word.Binds store ∧
    ramWord64? source address = some (Word.toBitVec64 row.1.ram.prior.value) ∧
    ramWord64? target address = some (Word.toBitVec64 row.1.ram.pushed.value) ∧
    Semantics.MemoryMsg.timeNat row.1.ram.prior = predecessor ∧
    Semantics.MemoryMsg.timeNat row.1.ram.pushed = request.clock + 1 ∧
    after (.ram (request.cell index)) = request.clock + 1 ∧
    ∀ data hint, (HintReadWordChip.circuit (request.last index)).ProverAssumptions row data hint

private theorem Request.wordAt_of_read (request : Request) {index : ℕ} {frontier after : AccessFrontier}
    {source target : SailState} {store : Store} (pos : index < wordCount request.bytes)
    (span : HintReadSpan.Domain request.address request.bytes.length) (fits : request.clock < 2 ^ 48)
    (phase : request.clock % 8 = 1) (pointer : 0 < request.pointer ∧ request.pointer < 2 ^ 48)
    (bounded : frontier.BoundedAt request.clock)
    (binding : (WordRecord.encode (p := SP1Prime) request.pointer request.bytes index).Binds store)
    (present : (ramWord64? source (BitVec.ofNat 64 (request.destination index))).isSome)
    (written : ramWord64? target (BitVec.ofNat 64 (request.destination index)) = some (wordValue request.bytes index))
    (posted : after (.ram (request.cell index)) = request.clock + 1) :
    request.WordAt index frontier after source target store := by
  have earlier := bounded (.ram (request.cell index))
  refine ⟨?_, rfl, ?_, ?_, ?_, previous_time (by omega) _ _, clock_time fits phase, posted,
    request.wordRow_assumptions _ span pos pointer fits phase earlier⟩
  · simp [rows, pos]
  · convert binding using 1
    change HintQueue.WordRecord.mk _ _ _ (if request.last index then _ else _) = _
    simp [last, WordRecord.encode]
    exact ⟨rfl, rfl, rfl⟩
  · change _ = some (Word.toBitVec64 (bitVecToWord (p := SP1Prime) _))
    rw [toBitVec64_bitVecToWord]
    cases found : ramWord64? source (BitVec.ofNat 64 (request.destination index)) <;> simp_all
  · change _ = some (Word.toBitVec64 (bitVecToWord (p := SP1Prime) _))
    rwa [toBitVec64_bitVecToWord]

private theorem head_of_cons {store : Store} {head : ℕ} {bytes : Bytes} {rest : List Bytes}
    (represented : Represents store head (bytes :: rest)) :
    ∃ tail, node? store head = some ⟨bytes, tail⟩ ∧ tail < head := by
  cases represented with
  | cons node decreasing _ => exact ⟨_, node, decreasing⟩

/-- At any actual HINT_READ cut of a native admissible eight-call execution, reconstruct the
complete ordered physical word batch from the persistent queue and the replayed Memory frontier.
Every active row meets the installed chip's completeness assumptions and carries the actual
incoming and outgoing Sail words. -/
theorem of_admissibleExecution {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (execution : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {cut : ℕ} {call : CoreSyscallEvent} (atEvent : events[cut]? = some (.syscall call))
    (read : call.rawCode = SyscallKind.hintRead.code) :
    let hostPolicy := policy SP1Prime image
    ∃ current next frontier cursor final bytes rest tail,
      mixedAccessPrefix hostPolicy image.program source.realize events cut = some (current, frontier) ∧
      mixedAccessPrefix hostPolicy image.program source.realize events (cut + 1) =
        some (next, syscallFrontier frontier current.clock call) ∧
      storeAfter? hostPolicy image.program source.realize (events.take cut) (ofList source.host.io.hints) = some cursor ∧
      storeAfter? hostPolicy image.program source.realize events (ofList source.host.io.hints) = some final ∧
      node? final.1 cursor.2 = some ⟨bytes, tail⟩ ∧ current.host.io.hints = bytes :: rest ∧
      next.host.io.hints = rest ∧ bytes.length = call.arg2.toNat ∧ current.clock = call.clock ∧
      HintReadSpan.Domain call.arg1.toNat bytes.length ∧
      let request : Request := ⟨call.clock, cursor.2, call.arg1.toNat, bytes⟩
      ∀ index < wordCount bytes, request.WordAt index frontier (syscallFrontier frontier current.clock call)
        current.sail next.sail final.1 := by
  obtain ⟨current, frontier, next, replay, built, step, nextBuilt, bounded, phase, fits, _⟩ :=
    admissibleExecution_syscall_from_prefix execution atEvent
  obtain ⟨reached, cursor, final, path, queueBuilt, represents, _, pointerBound, storeBound, _, finalBuilt, extend, _,
    records⟩ := admissibleExecution_hintInventory execution cut
  have same : reached = current := Option.some.inj (path.replay.symm.trans replay)
  subst reached
  cases step with
  | syscall success =>
    obtain ⟨pc, exec, _, _, ran, hostEq, sailEq, eventEq⟩ := HostState.step_observations success
    subst call
    have kind : exec.kind = .hintRead := SyscallKind.code_injective read
    have effect := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
    rw [kind] at effect
    obtain ⟨bytes, rest, queue, length, aligned, permitted, changeHost⟩ :=
      (HostState.execute_hintRead_iff ..).mp effect
    have span := HintReadSpan.domain_of_permitted bytes _ exec.arg1.toNat (by rfl) (by rfl) aligned permitted
    obtain ⟨write, hw, posting⟩ := syscallFrontier_hintRead ran kind frontier current.clock pc
    have written : exec.effect.write = some ⟨exec.arg1.toNat, hintWriteBytes bytes⟩ := by rw [changeHost]
    have writeEq := Option.some.inj (hw.symm.trans written)
    subst write
    rw [queue] at represents
    obtain ⟨tail, node, desc⟩ := head_of_cons represents
    let request : Request := ⟨current.clock, cursor.2, exec.arg1.toNat, bytes⟩
    refine ⟨current, _, frontier, cursor, final, bytes, rest, tail, built, nextBuilt, queueBuilt, finalBuilt,
      extend _ _ node, queue, ?_, length, rfl, span, ?_⟩
    · simp only [hostEq, changeHost]
    change ∀ index < wordCount bytes, request.WordAt index _ _ _ _ _
    intro index pos
    have inside := request.window span pos
    have destFits : request.destination index < 2 ^ 64 := by omega
    apply request.wordAt_of_read pos span (by exact Nat.lt_of_succ_lt fits) phase
      ⟨Nat.zero_lt_of_lt desc, pointerBound.trans_lt storeBound⟩ bounded
    · exact ((records _ _ node).2.2.2 index pos).2.2
    · apply ramWord64?_isSome_of_present
      intro offset small
      apply execution.1.memory_present_prefix replay
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destFits]
      change request.destination index + offset < 2 ^ 48
      omega
    · rw [sailEq]
      exact request.readback span pos current.sail exec pc written
    · rw [posting, ite_eq_left (request.cell_mem span pos)]

end SP1Clean.TraceGen.HintReadTransfers
