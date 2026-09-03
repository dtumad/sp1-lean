import SP1Clean.Faithful.SyscallInstrsChip
import SP1Clean.Faithful.CoreAIR
import SP1Clean.Model.Machine.Shard

/-! # What a syscall row means

The bridge from one `SyscallInstrsChip` row to one `Machine.CoreSyscallEvent`, and from the row's
constraints to that event's semantic laws. This is the layer at which "the chip is faithful to SP1's
AIR" becomes "the shard executed a syscall".

**The decoder is reused, not rewritten.** `Faithful.decodeSyscallRow` already maps an *extracted*
row to a `CoreSyscallEvent`, and `syscallInstrsReconfigure` maps a native row to an extracted one
index-for-index with both round-trips proved. Composing them is what makes this bridge land on the
same events `CoreAIRRefinementObligations` quantifies over; a fresh decoder would silently fail to
connect to the commit obligations.

**What the row gives, and what it does not.** Three of the four `RowLaw` conjuncts are the arm
`Spec`s almost verbatim — `WriteArm ↔ ResultLaw`, `PcArm ↔ PcLaw`, `DispatchArm ↔
HandlerAddressesFit`. What the row does **not** give, and must be supplied by the ensemble:

* the register indices `5`/`10`/`11` — SP1 does not pin them in the AIR either; the preprocessed
  Program table does, because the decoder always emits `Instruction::new(ECALL, X5, X10, X11)`;
* the `pc + 4` carry — upstream asserts `next_pc[0] = pc[0] + 4` with no carry into limb 1, and
  `StateBumpChip` is what legalizes the non-canonical result;
* canonicity of the syscall code — see `IsInlineCanonical` below.

**The canonicity premise (D9).** SP1's AIR reads only bytes 0 and 1 of `x5`; bytes 2–7 are free. The
executor instead dispatches on `x5 as u32` through `SyscallCode::from_u32`, which *panics* on any
non-enumerated value, and writes back `code as u64`. So an AIR-valid row may carry a `x5` that no
execution produces, and `IsCanonicalCode`/`SP1Halted` are not derivable from the row. Rather than
adding a constraint SP1 does not have — which is exactly the native-stricter pin `HaltChip` carries
today — canonicity is a **named profile premise**: true of every genuine execution, checkable on the
witness, and disclosed. All thirteen inline codes are `< 256`, so it reduces to "`x5`'s upper three
limbs vanish". -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.CoreAIR.Current (decodeSyscallRow)
open SP1Clean.Faithful (syscallInstrsReconfigure)
open SP1Clean.Soundness.Target (GuestProgram)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The row's event -/

/-- The event a native syscall row denotes, through the extracted decoder. -/
noncomputable def syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p)) : CoreSyscallEvent :=
  decodeSyscallRow (syscallInstrsReconfigure r)

/-- The event's syscall id is the chip's byte-0 selector input. This is the hinge of the whole
bridge: every arm `Spec` speaks of the selectors, every semantic law speaks of `syscallId`, and
`SelectorsValid`'s `U16toU8` decomposition is what ties them together. -/
theorem syscallId_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).syscallId = (SyscallInstrsChip.syscallId r).val := by
  -- SKETCH (L2): `rawCode` is `word64` of the four `op_a_memory.prev_value` limbs; the `U16toU8`
  -- spec gives `limb 0 = low_bytes[0] + high * 256` with both bytes `< 256`, so the word's low byte
  -- is `low_bytes[0]`.
  sorry

/-- The event's table byte is the chip's `tableByteVar` — the very multiplicity of the syscall-bus
send, which is why an unprovisioned bus forces it to zero. -/
theorem tableByte_syscallEventOfRow (r : SyscallInstrsChip.Inputs (ZMod p))
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1) :
    (syscallEventOfRow r).tableByte = (SyscallInstrsChip.tableByte r).val := by
  sorry

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

/-! ## The handler

Thirteen arms, dispatching on the id when the table byte is zero. The division of labour matters:
the handler supplies the **effect**, while `RowLaw` — which the row proves — says what the effect
must be. So the handler writes `event.result` to `t0` without itself deciding what `result` is;
`ResultLaw` is what pins it to `0` on ENTER_UNCONSTRAINED, to the oracle on HINT_LEN, and to the
unchanged code everywhere else. -/

/-- **The thirteen-arm handler.** HALT parks at `haltPc`; every other inline code advances one
instruction and writes `t0`. A non-zero table byte routes to a precompile and is not ours. -/
noncomputable def ExecutableSyscallHandler.full : ExecutableSyscallHandler where
  run := fun _program event source =>
    if event.tableByte ≠ 0 then none
    else if event.syscallId = Machine.haltSyscallId then
      some { source with regs := source.regs.insert Register.PC Machine.haltPc }
    else if event.syscallId ∈ inlineSyscallIds then
      some { source with
        regs := (source.regs.insert Register.PC (event.pc + 4)).insert Register.x5 event.result }
    else none

/-- `full` extends `haltOnly`: on a canonical HALT the two produce the same state, so every proof
that consumes the halt path keeps working when the binding is switched. -/
theorem full_run_eq_haltOnly_of_canonicalHalt (program : GuestProgram) (event : CoreSyscallEvent)
    (source : SailState) (h : event.IsCanonicalHalt) :
    ExecutableSyscallHandler.full.run program event source =
      ExecutableSyscallHandler.haltOnly.run program event source := by
  have hraw : event.rawCode = 0 := by
    simpa [CoreSyscallEvent.IsCanonicalHalt, CoreSyscallEvent.IsCanonicalCode] using h
  have hnat : event.rawCode.toNat = 0 := by rw [hraw]; rfl
  have htable : event.tableByte = 0 := by
    rw [CoreSyscallEvent.tableByte, hnat]
  have hid : event.syscallId = haltSyscallId := by
    rw [CoreSyscallEvent.syscallId, hnat]; rfl
  simp only [ExecutableSyscallHandler.full, ExecutableSyscallHandler.haltOnly, htable, hid,
    ne_eq, not_true_eq_false, if_false, if_true, if_pos hraw]

/-! ## The per-arm case theorems

One per inline arm, so that a missing arm is a missing theorem rather than a silent gap. Each says:
*this row's constraints, plus the named ensemble facts, give this arm's semantic transition.* The
exhaustiveness lemma at the end is what turns thirteen separate results into a total dispatch. -/

/-- The ensemble-supplied facts a syscall row needs beyond its own `Spec`. Naming them in one place
keeps the per-arm theorems honest about what is *not* row-local. -/
structure SyscallRowContext (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram)
    (source : SailState) : Prop where
  /-- The register operands are `x5`/`x10`/`x11`, from the Program bus's committed ECALL row. -/
  operands : r.op_a = 5 ∧ r.op_b = 10 ∧ r.op_c = 11
  /-- The pc's low limb does not carry, so `next_pc` recombines to `pc + 4`. Supplied by
  `StateBumpChip`, exactly as upstream intends. -/
  pcCarry : (r.state.pc[0]).val + 4 < 2 ^ 16
  /-- The row sits at an `ECALL` word of the committed program. -/
  ecall : Machine.AboutToExecuteEcall program source
  /-- The three pulled registers hold the row's prior words at this state. -/
  operandValues :
    source.get_reg? 5#5 = some (syscallEventOfRow r).rawCode ∧
    source.get_reg? 10#5 = some (syscallEventOfRow r).arg1 ∧
    source.get_reg? 11#5 = some (syscallEventOfRow r).arg2
  /-- The pc observation at the row's State pull. -/
  pcValue : source.regs.get? Register.PC = some (syscallEventOfRow r).pc

section Arms

variable (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram) (source : SailState)

/-- **RowLaw.** The row's own constraints give all four architecture-level laws. This is the part
that is genuinely row-local, and it is where `SelectorsValid` earns its place: without it no arm
`Spec` can be connected to `event.syscallId`. -/
theorem rowLaw_of_spec (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (pulled : SyscallInstrsChip.PulledFacts r)
    (real : r.is_real = 1) (ctx : SyscallRowContext r program source) :
    (syscallEventOfRow r).RowLaw := by
  -- SKETCH (L2): `WellRouted` from `GatesBoolean`'s boolean `tableByte`; `ResultLaw` from
  -- `WriteArm.Spec` + `SelectorsValid`; `PcLaw` from `PcArm.Spec` + `SelectorsValid` + `pcCarry`;
  -- `HandlerAddressesFit` from `DispatchArm.Spec` + `PulledFacts`' `isU64`.
  sorry

/-- **HALT.** The row parks the machine at `haltPc` and binds the exit code. -/
theorem arm_halt (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId = Machine.haltSyscallId)
    (ctx : SyscallRowContext r program source) :
    (syscallEventOfRow r).nextPc = Machine.haltPc := by
  sorry

/-- **ENTER_UNCONSTRAINED.** `t0 := 0`, one instruction on. The tracing VM returns `0` here (the
minimal executor's `1` is never traced), which is what the AIR's zero-word arm records. -/
theorem arm_enterUnconstrained (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.enterUnconstrainedSyscallId) :
    (syscallEventOfRow r).result = 0 := by
  sorry

/-- **HINT_LEN.** The only arm whose result is oracled; the row range-checks it and says no more. -/
theorem arm_hintLen (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.hintLenSyscallId) :
    Channels.MemoryMsg.isU64 ⟨0, 0, 0, 0, 0, r.op_a_value⟩ := by
  sorry

/-- **COMMIT.** No guest state changes; the meaning is the public-value digest binding, which lives
in the public-values layer because `SailState` carries no public values. -/
theorem arm_commit (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1) (hid : (syscallEventOfRow r).syscallId = Machine.commitSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode ∧
      (syscallEventOfRow r).arg1.toNat < 8 := by
  sorry

/-- **COMMIT_DEFERRED_PROOFS.** As COMMIT, with `a1` additionally a canonical field element — the
`32512` compare — because the deferred digest is stored as field elements. -/
theorem arm_commitDeferred (spec : SyscallInstrsChip.Spec r)
    (sel : SyscallInstrsChip.SelectorsValid r) (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId = Machine.commitDeferredSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode ∧
      SyscallInstrsChip.ExitCodeValid r.op_c_memory.prev_value := by
  sorry

/-- **The eight remaining inline codes.** WRITE, EXIT_UNCONSTRAINED, VERIFY_SP1_PROOF,
HINT_MPROTECT_FLUSH, DUMP_ELF, INSERT/DELETE_PROFILER_SYMBOLS and HINT_READ all share one arm: no
guest-state change beyond `pc + 4`, and `t0` unchanged. Upstream this is `Ok(None)`, which writes
`code as u64` — the same word, *given canonicity*. -/
theorem arm_default (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (real : r.is_real = 1)
    (hid : (syscallEventOfRow r).syscallId ≠ Machine.enterUnconstrainedSyscallId)
    (hid' : (syscallEventOfRow r).syscallId ≠ Machine.hintLenSyscallId) :
    (syscallEventOfRow r).result = (syscallEventOfRow r).rawCode := by
  sorry

end Arms

/-- **Coverage.** Under the canonicity premise and a zero table byte, the row's id is one of the
thirteen — so the arms above are a total dispatch and no case is silently unhandled. -/
theorem inlineSyscallIds_exhaustive (event : CoreSyscallEvent) (hc : event.IsInlineCanonical) :
    event.syscallId ∈ inlineSyscallIds := by
  rw [CoreSyscallEvent.syscallId_of_inlineCanonical hc]; exact hc

/-! ## The assembled transition -/

/-- **A syscall row executes a syscall.** The row's constraints, the ensemble's operand and carry
facts, and canonicity together give the full `SyscallTransition` against the thirteen-arm handler —
which is exactly what a walked syscall row must supply to the grounding engine. -/
theorem syscallTransition_of_row (r : SyscallInstrsChip.Inputs (ZMod p)) (program : GuestProgram)
    (source : SailState)
    (spec : SyscallInstrsChip.Spec r) (sel : SyscallInstrsChip.SelectorsValid r)
    (pulled : SyscallInstrsChip.PulledFacts r) (real : r.is_real = 1)
    (canonical : (syscallEventOfRow r).IsInlineCanonical)
    (ctx : SyscallRowContext r program source) :
    ∃ target : SailState,
      ExecutableSyscallHandler.full.run program (syscallEventOfRow r) source = some target ∧
      Machine.SyscallTransition ExecutableSyscallHandler.full.relation program
        (syscallEventOfRow r) source target := by
  -- SKETCH (L2): `RowLaw` from `rowLaw_of_spec`; `MatchesStates` from `ctx`'s observations and the
  -- handler's two inserts; the handler clause by `rfl` once the dispatch is unfolded at the row's
  -- id, which `inlineSyscallIds_exhaustive` makes total.
  sorry

end SP1Clean.Soundness
