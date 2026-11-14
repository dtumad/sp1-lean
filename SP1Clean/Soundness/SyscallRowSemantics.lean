import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal
import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.MicroTime

/-! # What a syscall row means

The native row decoder and the semantic laws proved from the row's constraints. Word values
use the library's little-endian limb decoding; no extracted Rust type participates in this
semantic boundary. Agreement with released SP1 is tested separately by Rust conformance tests.

**What the row gives, and what it does not.** Three of the four `RowLaw` conjuncts are the arm
`Spec`s almost verbatim — `WriteArm ↔ ResultLaw`, `PcArm ↔ PcLaw`, `DispatchArm ↔
HandlerAddressesFit`. What the row does **not** give, and must be supplied by the ensemble:

* the register indices `5`/`10`/`11` — SP1 does not pin them in the AIR either; the preprocessed
  Program table does, because the decoder always emits `Instruction::new(ECALL, X5, X10, X11)`;
* the full syscall code word — see below.

The Program bus's low-limb bound suffices to prove `nextPc = pc + 4`, even when the raw next
low limb exceeds `65535`. StateBump normalizes that representation separately.

**The full code word.** SP1's AIR selects from bytes 0 and 1 of `x5`. The executor dispatches on
`x5 as u32` through `SyscallCode::from_u32`, ignoring the upper 32 bits: `0x100000003` dispatches as
`ENTER_UNCONSTRAINED`. The semantic host step instead decodes the entire 64-bit word
(`SyscallKind.decode?`), so such a word is outside the semantic domain. The row alone does not
establish the full word. -/

open LeanRV64D

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Soundness.Target (GuestProgram)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The row's event -/

/-- The event denoted by a native syscall row. -/
noncomputable def syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p)) : CoreSyscallEvent where
  clock := r.state.clk_high.val * 2 ^ 24 + r.state.clk_16_24.val * 2 ^ 16 + r.state.clk_0_16.val
  pc := BitVec.ofNat 64
    (r.state.pc[0].val + r.state.pc[1].val * 2 ^ 16 + r.state.pc[2].val * 2 ^ 32)
  nextPc := BitVec.ofNat 64
    (r.next_pc[0].val + r.next_pc[1].val * 2 ^ 16 + r.next_pc[2].val * 2 ^ 32)
  rawCode := Word.toBitVec64 r.op_a_memory.prev_value
  arg1 := Word.toBitVec64 r.op_b_memory.prev_value
  arg2 := Word.toBitVec64 r.op_c_memory.prev_value
  result := Word.toBitVec64 r.op_a_value

/-- Lifting one byte split from the field to `ℕ`. The two bytes are each below `256`, so their
recombination is below `2 ^ 16` and cannot wrap the modulus — which is what `Fact (2 ^ 17 < p)` is
for. -/
private theorem byteSplit_val {a low high : ZMod p}
    (hlow : low.val < 256) (hhigh : high.val < 256) (h : a = low + high * 256) :
    a.val = low.val + high.val * 256 := by
  have hp : 2 ^ 17 < p := Fact.out
  have h256 : (256 : ZMod p).val = 256 := by
    have h : ((256 : ℕ) : ZMod p).val = 256 :=
      ZMod.val_natCast_of_lt (by omega)
    exact_mod_cast h
  have hmul : (high * 256 : ZMod p).val = high.val * 256 := by
    rw [ZMod.val_mul, h256]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h, ZMod.val_add, hmul]
  exact Nat.mod_eq_of_lt (by omega)

/-- The event's syscall id is the chip's byte-0 selector input. This is the hinge of the whole
bridge: every arm `Spec` speaks of the selectors, every semantic law speaks of `syscallId`, and
`SelectorsValid`'s `U16toU8` decomposition is what ties them together. -/
theorem syscallId_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).syscallId = (SyscallInstrsChip.syscallId r).val := by
  obtain ⟨hlow, hhigh, heq⟩ := sel.1 real 0
  -- the decomposition spec speaks at the operation's record projection; the row's own spelling is
  -- defeq to it, and `rw` needs the row's.
  have hlift : (r.op_a_memory.prev_value[0]).val
      = (SyscallInstrsChip.syscallId r).val
        + ((r.op_a_memory.prev_value[0] - r.syscall_id_bytes.low_bytes[0]) * 256⁻¹).val * 256 :=
    byteSplit_val hlow hhigh heq
  have hlow' : (SyscallInstrsChip.syscallId r).val < 256 := hlow
  change (Word.toBitVec64 r.op_a_memory.prev_value).toNat % 256 = _
  rw [Word.toBitVec64, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by norm_num : (256 : ℕ) ∣ 2 ^ 64), Word.toNat, hlift]
  omega

/-- The event's table byte is the chip's `tableByteVar` — the very multiplicity of the syscall-bus
send, which is why an unprovisioned bus forces it to zero. -/
theorem tableByte_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).tableByte = (SyscallInstrsChip.tableByte r).val := by
  obtain ⟨hlow, hhigh, heq⟩ := sel.1 real 0
  have hlift : (r.op_a_memory.prev_value[0]).val
      = (SyscallInstrsChip.syscallId r).val + (SyscallInstrsChip.tableByte r).val * 256 :=
    byteSplit_val hlow hhigh heq
  have hlow' : (SyscallInstrsChip.syscallId r).val < 256 := hlow
  have hhigh' : (SyscallInstrsChip.tableByte r).val < 256 := hhigh
  change (Word.toBitVec64 r.op_a_memory.prev_value).toNat / 256 % 256 = _
  rw [Word.toBitVec64, BitVec.toNat_ofNat, Word.toNat, hlift]
  omega

/-! ## The row's bus messages

The State edge and the committed fetch, at the ZMod level the ledger reads. These mirror
`HaltChip`'s, with two differences that are the whole point of the generalization: the pushed pc is
the row's own `next_pc` witness rather than the constant `haltPc`, and the fetch's operands are the
row's own cells rather than the literals `5`/`10`/`11`. -/

/-- The State message a syscall row pulls — the pre-syscall `(clk, pc)`. -/
def SyscallInstrsChip.statePulledMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536,
    r.state.pc[0], r.state.pc[1], r.state.pc[2]⟩

/-- The State message a syscall row pushes — `(clk + 264, next_pc)`. -/
def SyscallInstrsChip.statePushedMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.StateMsg (ZMod p) :=
  ⟨r.state.clk_high, r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 264,
    r.next_pc[0], r.next_pc[1], r.next_pc[2]⟩

/-- The Program message a syscall row pulls — the committed `ECALL op_a, op_b, op_c` at its pc. -/
def SyscallInstrsChip.programMessage (r : SyscallInstrsChip.Inputs (ZMod p)) :
    Channels.ProgramMsg (ZMod p) :=
  ⟨r.state.pc[0], r.state.pc[1], r.state.pc[2], 50,
   r.op_a, #v[r.op_b, 0, 0, 0], #v[r.op_c, 0, 0, 0], r.op_a_0, 0, 0⟩

/-- **The selector bridge.** The event's id matches a code exactly when the chip's field-level id
does. Every arm theorem goes through this: the arm `Spec`s are phrased over the `IsZero` selectors,
`SelectorsValid` phrases those over the *field* id, and the semantic laws phrase everything over the
event's *natural* id. Both directions are needed — the default arm's hypotheses are negations. -/
theorem syscallId_field_iff (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) {code : ℕ}
    (hcode : code < 256) :
    (syscallEventOfRow r).syscallId = code ↔ SyscallInstrsChip.syscallId r = (code : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hlt : (SyscallInstrsChip.syscallId r).val < 256 := (sel.1 real 0).1
  rw [syscallId_syscallEventOfRow r sel real]
  constructor
  · intro h
    have := congrArg (fun n : ℕ => (n : ZMod p)) h
    simpa [ZMod.natCast_val, ZMod.cast_id] using this
  · intro h
    rw [h, ZMod.val_natCast_of_lt (by omega : code < p)]

/-! ## The per-arm case theorems

One per inline arm, so that a missing arm is a missing theorem rather than a silent gap. Each says:
*this row's constraints, plus the named ensemble facts, give this arm's semantic transition.* The
exhaustiveness lemma at the end is what turns thirteen separate results into a total dispatch. -/

section Arms

variable (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram) (source : SailState)

/-! ### The event's fields, at the row's spelling

These unfold the native event decoder at an abstract row, keeping concrete row values opaque
in the arm proofs. -/

omit [Fact (2 ^ 17 < p)] in
theorem pc_syscallEventOfRow : (syscallEventOfRow r).pc = BitVec.ofNat 64
    ((r.state.pc[0]).val + (r.state.pc[1]).val * 2 ^ 16 + (r.state.pc[2]).val * 2 ^ 32) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem nextPc_syscallEventOfRow : (syscallEventOfRow r).nextPc = BitVec.ofNat 64
    ((r.next_pc[0]).val + (r.next_pc[1]).val * 2 ^ 16 + (r.next_pc[2]).val * 2 ^ 32) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem rawCode_syscallEventOfRow : (syscallEventOfRow r).rawCode = BitVec.ofNat 64
    ((r.op_a_memory.prev_value[0]).val + (r.op_a_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_a_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_a_memory.prev_value[3]).val * 2 ^ 48) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem result_syscallEventOfRow : (syscallEventOfRow r).result = BitVec.ofNat 64
    ((r.op_a_value[0]).val + (r.op_a_value[1]).val * 2 ^ 16 +
      (r.op_a_value[2]).val * 2 ^ 32 + (r.op_a_value[3]).val * 2 ^ 48) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem arg1_syscallEventOfRow : (syscallEventOfRow r).arg1 = BitVec.ofNat 64
    ((r.op_b_memory.prev_value[0]).val + (r.op_b_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_b_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_b_memory.prev_value[3]).val * 2 ^ 48) := rfl

omit [Fact (2 ^ 17 < p)] in
theorem arg2_syscallEventOfRow : (syscallEventOfRow r).arg2 = BitVec.ofNat 64
    ((r.op_c_memory.prev_value[0]).val + (r.op_c_memory.prev_value[1]).val * 2 ^ 16 +
      (r.op_c_memory.prev_value[2]).val * 2 ^ 32 +
      (r.op_c_memory.prev_value[3]).val * 2 ^ 48) := rfl

/-! ### The arms -/

/-- **HALT.** The row parks the machine at `haltPc`. `PcArm`'s halt branch pins the three pc limbs
to `(1, 0, 0)`, which recombines to `BitVec.ofNat 64 1` — SP1's `HALT_PC` exactly. -/
theorem arm_halt (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId = Machine.haltSyscallId) :
    (syscallEventOfRow r).nextPc = Machine.haltPc := by
  have hp : 2 ^ 17 < p := Fact.out
  have : Fact (1 < p) := ⟨by omega⟩
  have hfield : SyscallInstrsChip.syscallId r = ((SyscallInstrsChip.haltCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real (by decide : Machine.haltSyscallId < 256)).1 hid
  have hzero : r.is_halt_zero.result = 1 := by
    rw [(sel.2.1 real).1, ite_eq_left hfield]
  have hhalt : r.is_halt = 1 := by rw [sel.2.2.2.1, hzero, real, one_mul]
  have hpc : r.next_pc[0] = 1 ∧ r.next_pc[1] = 0 ∧ r.next_pc[2] = 0 :=
    spec.2.2.2.2.2.2.1.1 hhalt
  rw [nextPc_syscallEventOfRow, hpc.1, hpc.2.1, hpc.2.2, ZMod.val_one, ZMod.val_zero]
  rfl

/-- Program bounds suffice for the syscall PC increment. The low limb may carry into the
next 16-bit limb; only wrap in the ambient field must be excluded. -/
theorem arm_pcAdvance_of_pcBound (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId ≠ Machine.haltSyscallId)
    (pcBound : (r.state.pc[0]).val < 2 ^ 16) :
    (syscallEventOfRow r).nextPc = (syscallEventOfRow r).pc + 4 := by
  have hp : 2 ^ 17 < p := Fact.out
  have hfield : SyscallInstrsChip.syscallId r ≠ ((SyscallInstrsChip.haltCode : ℕ) : ZMod p) :=
    fun h => hid ((syscallId_field_iff r sel real (by decide : Machine.haltSyscallId < 256)).2 h)
  have hzero : r.is_halt_zero.result = 0 := by
    rw [(sel.2.1 real).1, ite_eq_right hfield]
  have hhalt : r.is_halt = 0 := by rw [sel.2.2.2.1, hzero, zero_mul]
  have hpc : r.next_pc[0] = r.state.pc[0] + 4 ∧ r.next_pc[1] = r.state.pc[1] ∧
      r.next_pc[2] = r.state.pc[2] := spec.2.2.2.2.2.2.1.2 real hhalt
  have hval : ((r.state.pc[0] + 4 : ZMod p)).val = (r.state.pc[0]).val + 4 := by
    have h4 : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    have : ((4 : ZMod p)).val = 4 := by rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, h4]
    rw [ZMod.val_add_of_lt (by rw [this]; omega), this]
  have harith : (r.state.pc[0]).val + 4 + (r.state.pc[1]).val * 2 ^ 16
        + (r.state.pc[2]).val * 2 ^ 32
      = ((r.state.pc[0]).val + (r.state.pc[1]).val * 2 ^ 16
        + (r.state.pc[2]).val * 2 ^ 32) + 4 := by ring
  rw [nextPc_syscallEventOfRow, pc_syscallEventOfRow, hpc.1, hpc.2.1, hpc.2.2, hval, harith]
  simp [BitVec.ofNat_add]

/-- **ENTER_UNCONSTRAINED.** `t0 := 0`. The tracing VM returns `0` here (the minimal executor's `1`
is never traced), which is what the AIR's zero-word arm records. The `op_a_0` booleanity the write
arm is reported under comes from the Program fetch, hence from `PulledFacts`. -/
theorem arm_enterUnconstrained (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.enterUnconstrainedSyscallId) :
    (syscallEventOfRow r).result = 0 := by
  have hfield :
      SyscallInstrsChip.syscallId r = ((SyscallInstrsChip.enterUnconstrainedCode : ℕ) : ZMod p) :=
    (syscallId_field_iff r sel real
      (by decide : Machine.enterUnconstrainedSyscallId < 256)).1 hid
  have henter : r.is_enter_unconstrained.result = 1 := by
    rw [(sel.2.1 real).2.1, ite_eq_left hfield]
  have hw : ∀ i : Fin 4, r.op_a_value[i] = 0 :=
    (spec.2.2.2.2.2.1 (pulled real).2.2.2.2.1).2.2.1 real henter
  have h0 : r.op_a_value[0] = 0 := hw 0
  have h1 : r.op_a_value[1] = 0 := hw 1
  have h2 : r.op_a_value[2] = 0 := hw 2
  have h3 : r.op_a_value[3] = 0 := hw 3
  rw [result_syscallEventOfRow, h0, h1, h2, h3, ZMod.val_zero]
  rfl

/-- **The eight remaining inline codes**, plus HALT, COMMIT and COMMIT_DEFERRED: `t0` is unchanged.
Upstream this is `Ok(None)`, which writes `code as u64` — the same word, *given canonicity*. The
write arm states it limb for limb, which is a genuine 64-bit equality. -/
theorem arm_default (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId ≠ Machine.enterUnconstrainedSyscallId)
    (hid' : (syscallEventOfRow r).syscallId ≠ Machine.hintLenSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode := by
  have hfe : SyscallInstrsChip.syscallId r
      ≠ ((SyscallInstrsChip.enterUnconstrainedCode : ℕ) : ZMod p) :=
    fun h => hid ((syscallId_field_iff r sel real
      (by decide : Machine.enterUnconstrainedSyscallId < 256)).2 h)
  have hfh : SyscallInstrsChip.syscallId r ≠ ((SyscallInstrsChip.hintLenCode : ℕ) : ZMod p) :=
    fun h => hid' ((syscallId_field_iff r sel real
      (by decide : Machine.hintLenSyscallId < 256)).2 h)
  have henter : r.is_enter_unconstrained.result = 0 := by
    rw [(sel.2.1 real).2.1, ite_eq_right hfe]
  have hhint : r.is_hint_len.result = 0 := by
    rw [(sel.2.1 real).2.2.1, ite_eq_right hfh]
  have hsum : r.is_enter_unconstrained.result + r.is_hint_len.result = 0 := by
    rw [henter, hhint, add_zero]
  have hw : ∀ i : Fin 4, r.op_a_value[i] = r.op_a_memory.prev_value[i] :=
    (spec.2.2.2.2.2.1 (pulled real).2.2.2.2.1).2.2.2 real hsum
  have h0 : r.op_a_value[0] = r.op_a_memory.prev_value[0] := hw 0
  have h1 : r.op_a_value[1] = r.op_a_memory.prev_value[1] := hw 1
  have h2 : r.op_a_value[2] = r.op_a_memory.prev_value[2] := hw 2
  have h3 : r.op_a_value[3] = r.op_a_memory.prev_value[3] := hw 3
  rw [result_syscallEventOfRow, rawCode_syscallEventOfRow, h0, h1, h2, h3]

/-- **RowLaw.** The row's own constraints give all four architecture-level laws. This is where
`SelectorsValid` earns its place: `ResultLaw` and `PcLaw` are `if`-then-`else` on the *event's* id,
while every arm `Spec` speaks of a selector column, and the selector bridge is the only thing that
connects them. Assembling the law from the arms — rather than proving it directly — is what makes a
missing arm a missing theorem. -/
theorem rowLaw_of_spec_and_pulledFacts (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) :
    (syscallEventOfRow r).RowLaw := by
  have hp : 2 ^ 17 < p := Fact.out
  have : Fact (1 < p) := ⟨by omega⟩
  have htb : (syscallEventOfRow r).tableByte = (SyscallInstrsChip.tableByte r).val :=
    tableByte_syscallEventOfRow r sel real
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `WellRouted`: the routing byte is boolean, which the row asserts ungated.
    rcases spec.1.2.2.2.2 with h | h
    · exact Or.inl (by rw [htb, h, ZMod.val_zero])
    · exact Or.inr (by rw [htb, h, ZMod.val_one])
  · -- `ResultLaw`: the three write arms, dispatched on the event's id.
    unfold CoreSyscallEvent.ResultLaw
    by_cases h3 : (syscallEventOfRow r).syscallId = Machine.enterUnconstrainedSyscallId
    · rw [ite_eq_left h3]; exact arm_enterUnconstrained r spec sel pulled real h3
    · rw [ite_eq_right h3]
      by_cases h240 : (syscallEventOfRow r).syscallId = Machine.hintLenSyscallId
      · rw [ite_eq_left h240]; trivial
      · rw [ite_eq_right h240]; exact arm_default r spec sel pulled real h3 h240
  · -- `PcLaw`: park at `haltPc`, or advance one instruction using the Program bus's low-limb bound.
    unfold CoreSyscallEvent.PcLaw
    by_cases h0 : (syscallEventOfRow r).syscallId = Machine.haltSyscallId
    · rw [ite_eq_left h0]; exact arm_halt r spec sel real h0
    · rw [ite_eq_right h0]; exact arm_pcAdvance_of_pcBound r spec sel real h0 (pulled real).2.1
  · -- `HandlerAddressesFit`: a dispatched row drops its fourth operand limb, leaving 48 bits.
    intro htable
    have hfield : SyscallInstrsChip.tableByte r = 1 := by
      rcases spec.1.2.2.2.2 with h | h
      · rw [CoreSyscallEvent.hasTable, htb, h, ZMod.val_zero] at htable
        exact absurd htable (by decide)
      · exact h
    have hdisp : r.op_b_memory.prev_value[3] = 0 ∧ r.op_c_memory.prev_value[3] = 0 :=
      spec.2.2.2.2.2.2.2.1 hfield
    have hb : Word.isU64 r.op_b_memory.prev_value := (pulled real).2.2.2.2.2.2.2.1
    have hc : Word.isU64 r.op_c_memory.prev_value := (pulled real).2.2.2.2.2.2.2.2.2.1
    have hb0 : (r.op_b_memory.prev_value[0]).val < 2 ^ 16 := hb 0
    have hb1 : (r.op_b_memory.prev_value[1]).val < 2 ^ 16 := hb 1
    have hb2 : (r.op_b_memory.prev_value[2]).val < 2 ^ 16 := hb 2
    have hc0 : (r.op_c_memory.prev_value[0]).val < 2 ^ 16 := hc 0
    have hc1 : (r.op_c_memory.prev_value[1]).val < 2 ^ 16 := hc 1
    have hc2 : (r.op_c_memory.prev_value[2]).val < 2 ^ 16 := hc 2
    constructor
    · rw [arg1_syscallEventOfRow, hdisp.1, ZMod.val_zero]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [arg2_syscallEventOfRow, hdisp.2, ZMod.val_zero]
      simp only [BitVec.toNat_ofNat]
      omega


end Arms

end SP1Clean.Soundness
