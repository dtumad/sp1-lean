import SP1Clean.Proofs.Completeness.WritePacketHandoff
import SP1Clean.Proofs.Completeness.WriteBufferBatch

/-! # Compiling the released instruction packet from the chronological physical span

The span's three clock limbs uniquely determine the native packet's four timestamp
pieces. Reconstructing the packet takes one pass over the ordered WRITE batch.
-/

namespace SP1Clean.WritePacket

open Circuit Air.Flat Semantics Machine Soundness.Target TraceGen FormalModel.Shard

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Recover a packet's four timestamp pieces directly from its three 16-bit header limbs. -/
def fromHeader (h : Header (ZMod p)) : Inputs (ZMod p) :=
  ⟨⟨h.clock[0], (h.clock[1].val % 256 : ℕ), (h.clock[1].val / 256 : ℕ), h.clock[2]⟩,
    h.descriptor, h.address, h.length⟩

/-- The reconstructed packet is honest and emits precisely the requested original header. -/
theorem fromHeader_spec (h : Header (ZMod p)) (clock : Address.Bounded h.clock) :
    (fromHeader h).timestamp.Bounded ∧ (fromHeader h).header = h := by
  have field := Fact.out (p := 2 ^ 24 < p)
  have middle : h.clock[1].val < 65536 := clock 1
  refine ⟨⟨clock 0, ?_, ?_, clock 2⟩, ?_⟩
  · change ((h.clock[1].val % 256 : ℕ) : ZMod p).val < _
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · change ((h.clock[1].val / 256 : ℕ) : ZMod p).val < _
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · have pack : ((h.clock[1].val % 256 : ℕ) : ZMod p) + (h.clock[1].val / 256 : ℕ) * (256 : ZMod p) = h.clock[1] := by
      have identity : h.clock[1].val % 256 + h.clock[1].val / 256 * 256 = h.clock[1].val := by omega
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : ZMod p)) identity
    cases h with
    | mk clk fd addr len =>
      change Header.mk #v[clk[0], _, clk[2]] fd addr len = Header.mk clk fd addr len
      apply congrArg (fun c => Header.mk c fd addr len)
      ext i bound
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · rfl
      · exact pack
      · rfl

/-- A bounded packet's own clock decomposition is unique. -/
theorem fromHeader_inverse (input : Inputs (ZMod p)) (bound : input.timestamp.Bounded) :
    fromHeader input.header = input := by
  rcases input with ⟨⟨lo, loMid, hiMid, hi⟩, fd, addr, len⟩
  obtain ⟨_, l, h, _⟩ := bound
  change loMid.val < 256 at l
  change hiMid.val < 256 at h
  have field := Fact.out (p := 2 ^ 24 < p)
  have packed : ((loMid.val + hiMid.val * 256 : ℕ) : ZMod p) = loMid + hiMid * 256 := by simp
  have value : (loMid + hiMid * 256).val = loMid.val + hiMid.val * 256 := by
    rw [← packed, ZMod.val_natCast_of_lt (by omega)]
  change Inputs.mk ⟨lo, ((loMid + hiMid * 256).val % 256 : ℕ), ((loMid + hiMid * 256).val / 256 : ℕ), hi⟩ fd addr len = _
  rw [value, show (loMid.val + hiMid.val * 256) % 256 = loMid.val by omega,
    show (loMid.val + hiMid.val * 256) / 256 = hiMid.val by omega, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- For each genuine batch entry the header constructor recovers the actual original ECALL
message and the same x12 word at that execution prefix. -/
theorem packet_input_at {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet}
    (run : AdmissibleExecution limits SP1Prime image source target events)
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets)
    {r : WriteBuffer.PacketRows (ZMod SP1Prime)} (member : r ∈ WriteBuffer.packetRows events packets) :
    let input := fromHeader r.span.header
    ∃ call current frontier, events[r.cut]? = some (.syscall call) ∧ call.rawCode = SyscallKind.write.code ∧
      mixedAccessPrefix (policy SP1Prime image) image.program source.realize events r.cut = some (current, frontier) ∧
      input.call = HostCallChip.message (syscallInstruction frontier call) ∧
      input.timestamp.Bounded ∧ input.header = r.span.header ∧
      current.sail.get_reg? 12 = some input.read.value.toBitVec64 := by
  obtain ⟨cut, call, current, frontier, len, buffer, present, write, reached, _, got, rfl⟩ :=
    WriteBuffer.packetRows_member run collected member
  obtain ⟨before, incoming, len', words, located, x12, observed, honest, callEq, stamp, fd, addr, length⟩ :=
    admissibleExecution_writePacket run present write
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (reached.symm.trans located))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (observed.symm.trans got))
  let i := populate (HostCallChip.message (syscallInstruction (p := SP1Prime) frontier call)) (bitVecToWord len')
  have checked : i.timestamp.Bounded := honest (.empty _) (.empty _)
  have canonical : Address.Bounded i.header.clock := i.timestamp.address_bounded checked
  have clock : i.header.clock = Address.ofNat call.clock := (Address.ofNat_toNat canonical).symm.trans (congrArg Address.ofNat stamp)
  have header : i.header = WriteBuffer.headerOfCall call.clock call len' := by
    have eq_header {a b : Header (ZMod SP1Prime)} (clock : a.clock = b.clock) (fd : a.descriptor = b.descriptor)
        (addr : a.address = b.address) (len : a.length = b.length) : a = b := by cases a; cases b; simp_all
    exact eq_header clock fd addr (show i.header.length = bitVecToWord len' from length)
  have original : fromHeader (WriteBuffer.makePacketRows (p := SP1Prime) (cut, call) (len', words)).span.header = i :=
    (congrArg fromHeader header.symm).trans (fromHeader_inverse i checked)
  dsimp only
  rw [original]
  exact ⟨call, _, _, present, write, reached, callEq, checked, header, by simpa [i, populate, Inputs.read, toBitVec64_bitVecToWord] using x12⟩

end SP1Clean.WritePacket
