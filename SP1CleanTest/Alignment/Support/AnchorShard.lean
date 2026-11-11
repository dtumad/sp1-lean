import SP1Clean.FormalModel.Execution
import SP1Clean.FormalModel.SupportedShard
import SP1Clean.FormalModel.TraceGen.Events
import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Soundness.ProviderBindings
import SP1Clean.FormalModel.Trace.Witness
import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.TransitionView
import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Model.SailDecode
import SP1CleanTest.TraceGenTests.Conformance
import SP1CleanTest.Core.StaticMembership
import ToClean.Air.TableEvaluation

/-! # The `JAL x0, 0` anchor shard

A shared semantic fixture: the program `JAL x0, 0` at `0x10000`, its configured Sail state, the
self-jump invariant giving code-memory compatibility along every reachable step, and the one
official-Sail step from that state. Its projection belongs to the supported 25-chip profile.
The legacy program-data codec below is a fixture input, not the canonical ensemble data.
-/

open LeanRV64D
open LeanRV64D.Functions

namespace SP1Clean.Audit.AnchorShard

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGenTests
open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Execution SP1Clean.TraceGen
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)
open Sail LeanRV64D LeanRV64D.Functions

local instance anchorDecidableEq : DecidableEq (ZMod SP1Prime) := FiniteField.instDecidableEq

/-! ## The committed program: `JAL x0, 0` at `0x10000`

One canonical ROM row `[pc0, pc1, pc2, w_lo, w_hi] = [0, 1, 0, 0x006F, 0]`: the self-jump
`JAL x0, 0` (encoding `0x0000006F`) at pc `0x10000 = 65536`.  The entry point and genesis clock are
the matching singleton keys. -/

/-- Legacy fixture encoding: one ROM row (`JAL x0, 0` at `0x10000`), entry point
`0x10000`, genesis clock `(0, 1)`, no data image. -/
def anchorData : ProverData (ZMod SP1Prime) where
  publicInput := #[]
  tables := fun key n =>
    match key, n with
    | "sp1.rom", 5 => #[#v[0, 1, 0, 111, 0]]
    | "sp1.pc_start", 3 => #[#v[0, 1, 0]]
    | "sp1.init_clk", 2 => #[#v[0, 1]]
    | _, _ => #[]

/-- The semantic guest program decoded from the fixture input. -/
def anchorProgram : GuestProgram := Commit.progOf anchorData

/-- The public State boundary: **initial = final** (clk `(0, 1)`, pc `(0, 1, 0)` = `0x10000` at
both ends), in the split-limb field order `clk_0_16, clk_16_24, clk_24_32, clk_32_48, pc0, pc1,
pc2` per end.  The recombination projections then give `init_clk_high = 0`, `init_clk_low = 1`
(and the same finally), so the verifier row's final-state pull and initial-state push are the same
State message with cancelling multiplicities, exactly as before the split. -/
theorem anchorProgram_rom :
    anchorProgram.rom = [(65536#64, (0x0000006F : BitVec 32))] := by native_decide

/-- The committed data image is empty. -/
theorem anchorProgram_memImage :
    anchorProgram.memImage = ([] : List (BitVec 64 × BitVec 8)) := by native_decide

/-- The only fetchable address/word pair is the committed self-jump. -/
theorem anchorProgram_fetchWord {a : BitVec 64} {w : BitVec 32}
    (hf : anchorProgram.fetchWord a = some w) :
    a = 65536#64 ∧ w = (0x0000006F : BitVec 32) := by
  rw [GuestProgram.fetchWord, anchorProgram_rom] at hf
  by_cases ha : (65536#64 : BitVec 64) = a
  · rw [List.find?_cons_of_pos (by simp [ha])] at hf
    simp only [Option.map_some, Option.some_inj] at hf
    exact ⟨ha.symm, hf.symm⟩
  · rw [List.find?_cons_of_neg (by simpa using ha), List.find?_nil] at hf
    simp at hf

/-- The one-instruction program satisfies the loader-facing well-formedness contract.  This is the
field the ROM-free `emptyProgram` cannot satisfy (`entryPointPresent` demands a fetchable entry
instruction), which is why the joint witness commits a real instruction. -/
theorem anchorProgram_wellFormed : anchorProgram.WellFormed where
  entryPointPresent := ⟨0x0000006F, by native_decide⟩
  imageAddressesUnique := by
    rw [GuestProgram.ImageAddressesUnique, anchorProgram_memImage]
    simp
  imageCompatibleWithROM := by
    intro address instruction hfetch index imageEntry hmem
    rw [anchorProgram_memImage] at hmem
    simp at hmem

/-- The concrete committed ROM/image row lists. -/
theorem anchorData_romRows :
    Commit.romRowsOf (p := SP1Prime) anchorData = [#v[0, 1, 0, 111, 0]] := by native_decide

theorem anchorData_imageRows :
    Commit.imageRowsOf (p := SP1Prime) anchorData = [] := by native_decide

/-- Boolean-checker bridge for the limb-range side conditions.  A bounded `∀ v ∈ l, …` over
`ZMod SP1Prime` must NOT be handed to `decide`/`native_decide` directly: instance synthesis picks
`Fintype.decidableForallFintype` over the 2^31-element field, not `List.decidableBAll`.  The `Bool`
`List.all` form evaluates over just the list. -/
theorem rowValuesBelow_of_all {n bound : ℕ} (row : Vector (ZMod SP1Prime) n)
    (h : row.toList.all (fun v => decide (v.val < bound)) = true) :
    Commit.RowValuesBelow bound row := by
  intro value hvalue
  exact of_decide_eq_true (List.all_eq_true.mp h value hvalue)

/-- The committed representation is canonical: nothing is sanitized away, all limbs are in range,
and the singleton keys are singletons. -/
theorem anchorData_canonicalEncoding : Commit.CanonicalEncoding (p := SP1Prime) anchorData := by
  refine ⟨by native_decide, ?_, ?_, ?_,
    ⟨#v[0, 1, 0], by native_decide, rowValuesBelow_of_all _ (by native_decide)⟩,
    ⟨#v[0, 1], by native_decide, rowValuesBelow_of_all _ (by native_decide)⟩⟩
  · rw [anchorData_romRows]
    intro row hrow
    rw [List.mem_singleton] at hrow
    subst hrow
    exact rowValuesBelow_of_all _ (by native_decide)
  · rw [anchorData_imageRows]
    intro row hrow
    exact absurd hrow (List.not_mem_nil)
  · rw [anchorData_imageRows]
    simp

/-! ## The joint witness: 52 zero-row tables, the two Byte providers, and the Halt padding row

Every table except the two byte providers and the Halt table has zero rows. The provider rows are
honest witnesses of their circuits: input cells first (`ProvableType` order, including the explicit
multiplicity), then the `rangeCheck n` subcircuits' local bit-decomposition cells in emission
order. -/

/-- A zero-row table, with the component's fixed-column obligation checked explicitly. -/
noncomputable def anchorMem : Std.ExtHashMap ℕ (BitVec 8) :=
  (((((configuredState (65536#64)).mem.insert 65536 (0x6F : BitVec 8)).insert
    65537 (0x00 : BitVec 8)).insert 65538 (0x00 : BitVec 8)).insert 65539 (0x00 : BitVec 8))

/-- The concrete initial state: every register initialized, pc pinned to the self-jump, machine
mode, SP1 PMA region, and the instruction bytes in memory. -/
noncomputable def anchorState : SailState :=
  { configuredState (65536#64) with mem := anchorMem }

theorem anchorMem_65536 : anchorMem.get? 65536 = some (0x6F : BitVec 8) := by
  show anchorMem[(65536 : ℕ)]? = some (0x6F : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, ite_eq_right (by decide), Std.ExtHashMap.getElem?_insert,
    ite_eq_right (by decide), Std.ExtHashMap.getElem?_insert, ite_eq_right (by decide),
    Std.ExtHashMap.getElem?_insert, ite_eq_left (by decide)]

theorem anchorMem_65537 : anchorMem.get? 65537 = some (0x00 : BitVec 8) := by
  show anchorMem[(65537 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, ite_eq_right (by decide), Std.ExtHashMap.getElem?_insert,
    ite_eq_right (by decide), Std.ExtHashMap.getElem?_insert, ite_eq_left (by decide)]

theorem anchorMem_65538 : anchorMem.get? 65538 = some (0x00 : BitVec 8) := by
  show anchorMem[(65538 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, ite_eq_right (by decide), Std.ExtHashMap.getElem?_insert,
    ite_eq_left (by decide)]

theorem anchorMem_65539 : anchorMem.get? 65539 = some (0x00 : BitVec 8) := by
  show anchorMem[(65539 : ℕ)]? = some (0x00 : BitVec 8)
  unfold anchorMem
  rw [Std.ExtHashMap.getElem?_insert, ite_eq_left (by decide)]

theorem anchorState_pc : anchorState.regs.get? Register.PC = some (65536#64) :=
  cfgState_pc (65536#64)

/-- The full platform configuration of `configuredState`, generalized over the pc (the inline
`configured` block of `isInitialState_nonvacuous`, made reusable). -/
theorem configuredState_sailConfigured (pc : BitVec 64) : SailConfigured (configuredState pc) where
  init := cfgState_init pc
  priv := cfgState_priv pc
  active := by
    rw [cfgState_get?_other pc Register.hart_state (by decide) (by decide) (by decide) (by decide)]
    rfl
  mie := by
    rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : _get_Mstatus_MIE (default : RegisterType Register.mstatus) = 0#1)
  mideleg := by
    rw [cfgState_get_other pc Register.mideleg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : (default : RegisterType Register.mideleg) = zeros)
  no_landing_pad := by
    rw [cfgState_get?_other pc Register.elp (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : ¬ (some (default : RegisterType Register.elp)
      = some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)))
  mprv_disabled := by
    rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 1 ((default : RegisterType Register.mstatus).toNat >>> 17) = 0#1)
  mseccfg_disabled := by
    rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 1 ((default : RegisterType Register.mseccfg).toNat >>> 10) = 0#1)
  mseccfg_pmm := by
    rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
    exact (by decide :
      BitVec.ofNat 2 ((default : RegisterType Register.mseccfg).toNat >>> 32) = 0#2)
  htif_disabled := by
    rw [cfgState_get_other pc Register.htif_tohost_base (by decide) (by decide) (by decide)
      (by decide)]
    exact (by decide : (default : RegisterType Register.htif_tohost_base) = none)
  pmp_off := by
    rw [cfgState_get_other pc Register.pmpcfg_n (by decide) (by decide) (by decide) (by decide)]
    exact (by decide : (default : RegisterType Register.pmpcfg_n) = Vector.replicate 64 0#8)
  misa_m := by
    rw [cfgState_misa pc _]
    decide
  misa_c_disabled := by
    rw [cfgState_misa pc _]
    decide
  pma_regions := cfgState_pma pc _

/-- The enriched state keeps the register-only configuration (the memory update is invisible to
every `SailConfigured` field). -/
theorem anchorState_configured : SailConfigured anchorState :=
  let base := configuredState_sailConfigured (65536#64)
  { init := base.init
    priv := base.priv
    active := base.active
    mie := base.mie
    mideleg := base.mideleg
    no_landing_pad := base.no_landing_pad
    mprv_disabled := base.mprv_disabled
    mseccfg_disabled := base.mseccfg_disabled
    mseccfg_pmm := base.mseccfg_pmm
    htif_disabled := base.htif_disabled
    pmp_off := base.pmp_off
    misa_m := base.misa_m
    misa_c_disabled := base.misa_c_disabled
    pma_regions := base.pma_regions }

/-- The committed ROM's bytes are loaded in the witness state, little-endian. -/
theorem anchorState_romLoaded : RomLoaded anchorProgram anchorState := by
  intro a w hf i
  obtain ⟨rfl, rfl⟩ := anchorProgram_fetchWord hf
  fin_cases i
  · exact anchorMem_65536
  · exact anchorMem_65537
  · exact anchorMem_65538
  · exact anchorMem_65539

/-! ## Conjunct 2: the semantic boundary binding -/

theorem supportedPcBits_anchor :
    supportedPcBits (0 : ZMod SP1Prime) 1 0 = 65536#64 := by native_decide

/-! ### Closing `SailCodeMemoryCompatible`: the self-jump step invariant

`JAL x0, 0` jumps to its own address and commits no register write and no memory write, so every
reachable Sail state keeps pc `0x10000`, the ROM bytes, and the platform configuration.  One
application of the proved `advance_of_jal_x0` per step, plus determinism of the `EStateM`
interpreter run, closes the boundary contract outright — no preservation assumption remains. -/

/-- A zeroed register-access block (gated off on the J-type row; never read by `advance`). -/
def zeroAccess : Circuits.Types.RegisterAccessCols (ZMod SP1Prime) := ⟨#v[0, 0, 0, 0], ⟨0, 0⟩⟩

/-- The row view of the committed self-jump: opcode JAL, destination `x0`, immediate `op_b = 0`,
current and next pc both `0x10000`, no commit effect. -/
def jalView : Trace.RowView (ZMod SP1Prime) where
  state := { clk_high := 0, clk_16_24 := 0, clk_0_16 := 1, pc := #v[0, 1, 0] }
  next_pc := #v[0, 1, 0]
  adapter :=
    { op_a := 0, op_a_memory := zeroAccess, op_a_0 := 1,
      op_b := bitVecToWord ((0#21 : BitVec 21).signExtend 64), op_b_memory := zeroAccess,
      imm_b := 1,
      op_c := #v[0, 0, 0, 0], op_c_memory := zeroAccess, imm_c := 1 }
  is_real := 1
  rdWrite := #v[0, 0, 0, 0]
  opcode := ((Opcode.JAL).toNat : ZMod SP1Prime)
  commit := .noWrite

theorem jalView_rcvPc : rcvPcOf (stateAccess jalView) = 65536#64 := by native_decide

theorem jalView_sndPc : sndPcOf (stateAccess jalView) = 65536#64 := by native_decide

/-- The official decoder on the committed word `0x0000006F` is `JAL x0, 0` (the `decode_JAL`
recipe of `Model/SailDecode.lean`, at the self-jump word). -/
theorem decode_jal_x0 (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (runSail (ext_decode 0x0000006F#32)) s
      = .ok (instruction.JAL (0#21, regidx.Regidx 0#5)) s := by
  conv_lhs => arg 1; whnf
  rw [SailDecode.cePause_apply]
  conv_lhs => arg 1; whnf
  rw [SailDecode.free_bind_eq_bind, bind_assoc, SailDecode.ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => arg 1; whnf
  rfl

/-- The committed Program row of the self-jump view is the decode of the fetched ROM word. -/
theorem jalView_decodedInROM :
    decodedInROM (p := SP1Prime) anchorProgram (programAccess jalView).toRow := by
  refine ⟨0x0000006F#32, .JAL (0#21, .Regidx 0#5), ?_, ?_, ?_⟩
  · native_decide
  · intro s hs
    exact decode_jal_x0 s hs.init hs.priv hs.mseccfg_disabled
  · rfl

/-- The persistent step invariant: pc at the self-jump, ROM loaded, configuration intact. -/
def AnchorInv (s : SailState) : Prop :=
  s.regs.get? Register.PC = some (65536#64) ∧ RomLoaded anchorProgram s ∧ SailConfigured s

theorem anchorInv_base : AnchorInv anchorState :=
  ⟨anchorState_pc, anchorState_romLoaded, anchorState_configured⟩

/-- The committed self-jump takes one official Sail step and exposes the exact row effect used by
both the reachability invariant and the active deterministic-compiler audit. -/
theorem anchorStep :
    ∃ next, SailStep anchorState next ∧ RowEffect anchorProgram jalView anchorState next := by
  exact Advance.advance_of_jal_x0 (p := SP1Prime) (prog := anchorProgram) (r := jalView)
    anchorState_configured anchorState_romLoaded
    (by rw [jalView_rcvPc]; exact anchorState_pc) jalView_decodedInROM rfl rfl rfl
    (by rw [jalView_sndPc]; decide)
    (fun imm hb => by
      have hb' : bitVecToWord (p := SP1Prime) ((0#21 : BitVec 21).signExtend 64) =
          bitVecToWord (imm.signExtend 64) := hb
      have h64 := congrArg Word.toBitVec64 hb'
      rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at h64
      rw [jalView_rcvPc, jalView_sndPc,
        show sign_extend (m := 64) imm = imm.signExtend 64 from rfl, ← h64]
      decide)

/-- One interpreter step from an invariant state re-establishes the invariant: the step is the
committed self-jump (`advance_of_jal_x0` plus determinism of the `EStateM` run), whose `RowEffect`
commits pc `0x10000` with no register write, no memory write, and configuration persistence. -/
theorem anchorInv_step {s next : SailState} (inv : AnchorInv s) (step : SailStep s next) :
    AnchorInv next := by
  obtain ⟨hpc, hrom, hcfg⟩ := inv
  obtain ⟨s', hstep', heff⟩ :=
    Advance.advance_of_jal_x0 (p := SP1Prime) (prog := anchorProgram) (r := jalView)
      hcfg hrom (by rw [jalView_rcvPc]; exact hpc) jalView_decodedInROM rfl rfl rfl
      (by rw [jalView_sndPc]; decide)
      (fun imm hb => by
        have hb' : bitVecToWord (p := SP1Prime) ((0#21 : BitVec 21).signExtend 64) =
            bitVecToWord (imm.signExtend 64) := hb
        have h64 := congrArg Word.toBitVec64 hb'
        rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at h64
        rw [jalView_rcvPc, jalView_sndPc,
          show sign_extend (m := 64) imm = imm.signExtend 64 from rfl, ← h64]
        decide)
  obtain ⟨b, hb⟩ := step
  obtain ⟨b', hb'⟩ := hstep'
  have hnext : next = s' := by
    have hok := hb.symm.trans hb'
    injection hok
  subst hnext
  refine ⟨?_, ?_, heff.cfg hcfg⟩
  · rw [heff.pc, jalView_sndPc]
  · intro a w hf i
    rw [heff.mem.1 rfl]
    exact hrom a w hf i

theorem anchorInv_of_chain {n : ℕ} {a b : SailState}
    (inva : AnchorInv a) (chain : Target.SailChain n a b) : AnchorInv b := by
  induction chain with
  | refl s => exact inva
  | step h1 _ ih => exact ih (anchorInv_step inva h1)

/-- ROM preservation along every reachable Sail step: reachable states satisfy the self-jump
invariant, and each further step re-establishes it — in particular `RomLoaded` persists. -/
theorem anchor_codeMemoryCompatible : SailCodeMemoryCompatible anchorProgram anchorState := by
  intro n state next chain step _hromState
  exact (anchorInv_step (anchorInv_of_chain anchorInv_base chain) step).2.1

/-! ## The official-Sail self-jump step -/

/-- The deterministic target of the proved official-Sail self-jump. -/
noncomputable def activeTarget : SailState := Classical.choose anchorStep

theorem activeTarget_step : SailStep anchorState activeTarget :=
  (Classical.choose_spec anchorStep).1

/-- The chosen official-Sail target has the exact JAL row effect used by the trace schema. -/
theorem activeTarget_effect :
    RowEffect anchorProgram jalView anchorState activeTarget :=
  (Classical.choose_spec anchorStep).2

/-- The one-transition official-Sail execution used to audit the native compiler. -/
noncomputable def activeExecution : Machine.EventExecutionTrace where
  initialState := anchorState
  transitions := [⟨.ordinary, activeTarget⟩]

@[simp] theorem activeExecution_initialState : activeExecution.initialState = anchorState := rfl

@[simp] theorem activeExecution_transitions :
    activeExecution.transitions = [⟨.ordinary, activeTarget⟩] := rfl

@[simp] theorem activeExecution_steps : activeExecution.steps = 1 := rfl

@[simp] theorem activeExecution_finalState : activeExecution.finalState = activeTarget := rfl

@[simp] theorem activeExecution_locatedTransitions :
    activeExecution.locatedTransitions =
      [⟨anchorState, ⟨.ordinary, activeTarget⟩⟩] := rfl

/-- Fetching the committed entry point yields the self-jump encoding. -/
theorem anchorProgram_fetchWord_selfJump :
    anchorProgram.fetchWord 65536#64 = some 0x0000006F#32 := by
  native_decide

/-- The configured Sail decoder recognizes the committed word as `JAL x0, 0`. -/
theorem anchor_decode_selfJump :
    (runSail (ext_decode 0x0000006F#32)) anchorState =
      .ok (instruction.JAL (0#21, .Regidx 0#5)) anchorState :=
  decode_jal_x0 anchorState anchorState_configured.init anchorState_configured.priv
    anchorState_configured.mseccfg_disabled

/-- The committed self-jump is not an ECALL. -/
theorem anchor_notAboutToExecuteEcall :
    ¬ Machine.AboutToExecuteEcall anchorProgram anchorState := by
  rintro ⟨pc, pcEq, fetch⟩
  rw [anchorState_pc] at pcEq
  injection pcEq with pcEq
  subst pc
  rw [anchorProgram_fetchWord_selfJump] at fetch
  exact (by native_decide : (0x0000006F#32 : BitVec 32) ≠ ECALL_ENC)
    (Option.some.inj fetch)

/-- The proof-free transition list is authenticated by the official Sail step. -/
theorem activeExecution_valid :
    activeExecution.Valid Machine.ExecutableSyscallHandler.haltOnly.relation anchorProgram := by
  exact .cons ⟨.ordinary, activeTarget⟩
    (.ordinary anchor_notAboutToExecuteEcall activeTarget_step) (.nil activeTarget)

theorem activeExecution_allOrdinary : activeExecution.AllOrdinary := by
  intro transition member
  simp only [activeExecution, List.mem_singleton] at member
  subst transition
  rfl

/-- The exact proof-independent projection shared by semantic validity and trace compilation. -/
noncomputable def activeView : SP1Clean.Semantics.SP1TransitionView where
  pc := 65536#64
  word := 0x0000006F#32
  decoded := .JAL (0#21, .Regidx 0#5)
  routeKey := ⟨.JAL, true⟩
  chipId := .jal
  accessPlan? := SP1Clean.Semantics.instructionAccessPlan?
    (.JAL (0#21, .Regidx 0#5)) anchorState activeTarget

theorem activeExecution_projected :
    SP1Clean.Semantics.projectSP1Transition? anchorProgram
      ⟨anchorState, ⟨.ordinary, activeTarget⟩⟩ = some activeView := by
  unfold SP1Clean.Semantics.projectSP1Transition?
  simp only [anchorState_pc, Option.bind_eq_bind, Option.bind_some,
    anchorProgram_fetchWord_selfJump]
  rw [SP1Clean.Semantics.decodeLocated?_eq_some_of anchorState_pc
    anchorProgram_fetchWord_selfJump anchor_decode_selfJump]
  rfl

theorem activeExecution_configuredDecode :
    ConfiguredDecode activeView.word activeView.decoded := by
  intro state configured
  exact decode_jal_x0 state configured.init configured.priv configured.mseccfg_disabled

/-- The active transition belongs to the exact supported 25-chip profile. -/
theorem activeExecution_supported :
    AllTransitionsSupported anchorProgram activeExecution := by
  intro located member _
  rw [activeExecution_locatedTransitions, List.mem_singleton] at member
  subst located
  exact ⟨rfl, activeTarget_effect.normal, anchorState_configured, activeView,
    activeExecution_projected, activeExecution_configuredDecode⟩


end SP1Clean.Audit.AnchorShard
