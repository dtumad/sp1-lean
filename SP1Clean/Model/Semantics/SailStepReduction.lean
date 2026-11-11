import SP1Clean.Model.SailWrap
import SP1Clean.Model.SailMemory
import SP1Clean.Model.Semantics.GuestProgram
import SP1Clean.Model.SailPlatform

/-! # Official Sail fetch, dispatch and retirement reduction

Reduce the generated step through ArchSem's interpreter. Interrupt refresh, fetched-instruction
metadata, execution redirection and retirement bookkeeping remain part of the observed step.
-/

open LeanRV64D
namespace SP1Clean.TryStepReduction

open Sail Sail.ArchSem LeanRV64D LeanRV64D.Functions
open SP1Clean

/-! ## Stage 0 — the pure config / hook flags (constants in the Sail model) -/

/-- The instruction-print config flag is compile-time `false` (`Prelude.lean:219`), so the fetch/step
print branches are dead. -/
@[simp] theorem get_config_print_instr_eq : get_config_print_instr () = false := rfl

/-- The RVFI config flag is compile-time `false` (`Prelude.lean:237`), so `fetch` takes its non-RVFI
branch and the step's `rvfi_pc_data` write is dead. -/
@[simp] theorem get_config_rvfi_eq : get_config_rvfi () = false := rfl

/-- The fetch hook is the identity (`StepExt.lean:207`). -/
@[simp] theorem ext_fetch_hook_eq (f : FetchResult) : ext_fetch_hook f = f := rfl

/-- The pre-step hook is a no-op (`StepExt.lean:210`). -/
@[simp] theorem ext_pre_step_hook_eq : ext_pre_step_hook () = () := rfl

/-- The post-step hook is a no-op (`StepExt.lean`). -/
@[simp] theorem ext_post_step_hook_eq : ext_post_step_hook () = () := rfl

/-- `hart_is_active` on the active hart is `true` (`StepCommon.lean:207`). -/
@[simp] theorem hart_is_active_active : hart_is_active (HartState.HART_ACTIVE ()) = true := rfl

/-! ## Stage 1 — the `readReg`-then-`pure` aux stages -/

/-- `is_landing_pad_expected () = pure (readReg elp == LP_EXPECTED_bits)` (`ZicfilpRegs.lean:252`) reduces,
under `isInitialized`, to the boolean comparison of the state's `elp` against the landing-pad-expected
encoding — no state change. The straight-line path wants this `false` (`elp = NO_LP_EXPECTED`). -/
theorem run_is_landing_pad_expected (s : SailState) (hs : SailState.isInitialized s) :
    (runSail (is_landing_pad_expected ())) s
      = .ok (s.regs.get Register.elp (hs _)
          == landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED) s := by
  unfold is_landing_pad_expected
  rw [Sail.run_readReg_bind_of_isInitialized s Register.elp hs]
  simp only [runSail_pure]

/-- `should_inc_minstret priv` (`Platform.lean:537`) reads `mcountinhibit` + `minstretcfg` and returns a
boolean, no state change. Whatever the boolean is, `try_step`'s `writeReg minstret_increment (← should_…)`
only touches the (unobservable) `minstret_increment` register — the frame fact the reduction needs. -/
theorem run_should_inc_minstret (s : SailState) (hs : SailState.isInitialized s) (priv : Privilege) :
    (runSail (should_inc_minstret priv)) s
      = .ok (((_get_Counterin_IR (s.regs.get Register.mcountinhibit (hs _))) == 0#1)
          && ((counter_priv_filter_bit (s.regs.get Register.minstretcfg (hs _)) priv) == 0#1)) s := by
  simp only [should_inc_minstret, andM, toBool,
    Sail.run_readReg_bind_of_isInitialized s Register.mcountinhibit hs, pure_bind]
  split <;> simp_all only [Bool.false_and, Bool.true_and,
    Sail.run_readReg_bind_of_isInitialized s Register.minstretcfg hs, runSail_pure]

/-! ## Stage 2 — the straight-line readiness predicate

The state facts a real ROM-loaded, quiescent, machine-mode SP1 execution state carries, bundling the two
*deep* Sail-side facts (interrupt-quiescence and ROM-fetch) as fields so the `run_hart_active`/`try_step`
composition can thread them; each is discharged separately from the Sail model (Stages 2'/3' — the
`dispatchInterrupt`/`fetch` reductions, which spiral through `getPendingSet`/`read_mip`/`currentlyEnabled`
and `fetch_bytes`/`translateAddr`/`mem_read`). `w` is the fetched instruction word. -/
structure StraightLineReady (s : SailState) (w : BitVec 32) : Prop where
  /-- CSRs present (the Sail-model reduction residue). -/
  init : s.isInitialized
  /-- Machine mode. -/
  priv : s.regs.get? Register.cur_privilege = some Privilege.Machine
  /-- The hart is active (not waiting). -/
  active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  /-- No interrupt is dispatched — the interior of `run_hart_active`'s first stage runs to `none` (Stage
  2'; holds when machine interrupts are disabled, `mstatus.MIE = 0`, since `getPendingSet` short-circuits
  on `mIE`). -/
  no_interrupt : (runSail (dispatchInterrupt Privilege.Machine)) s = .ok none s
  /-- The fetch yields the base (32-bit) ROM word `w` (Stage 3'; from `RomLoaded` + PC-aligned + no
  translation fault). -/
  fetched : (runSail (fetch ())) s = .ok (FetchResult.F_Base w) s
  /-- No landing pad is expected (`elp ≠ LP_EXPECTED`), so the CFI trap branch is dead. -/
  no_landing_pad :
    s.regs.get? Register.elp ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)

/-! ## Stage 3 — `run_hart_active` reduces to the execute stage -/

/-- Fetch and decode select the actual instruction and preserve the metadata used at retirement. -/
theorem run_hart_active_eq_of_ready (s : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (h : StraightLineReady s w) (hdec : runSail (ext_decode w) s = .ok I s) :
    runSail (run_hart_active step_no) s = runSail (do
      LeanRV64D.writeReg Register.nextPC (BitVec.addInt (← LeanRV64D.readReg Register.PC) 4)
      let (executed, result) ← match (← execute I) with
        | .ExecuteAs other => do pure (some other, ← execute other)
        | result => pure (some I, result)
      pure (Step.Step_Execute (result, {
        fetch_privilege := .Machine
        fetch_trigger_reentrance := _get_Mstatus_MIE (s.regs.get Register.mstatus (h.init _)) == 0#1
        fetched_instruction := I
        executed_instruction := executed
        instbits := zero_extend w
        compressed := false }))) s := by
  have hl : runSail (is_landing_pad_expected ()) s = .ok false s := by
    rw [run_is_landing_pad_expected s h.init]
    congr 1
    rw [beq_eq_false_iff_ne]
    exact fun same => h.no_landing_pad
      (by rw [Std.ExtDHashMap.get?_eq_some_get (h.init _), same])
  have hcp : runSail (LeanRV64D.readReg Register.cur_privilege) s = .ok Privilege.Machine s := by
    rw [LeanRV64D.readReg, Sail.run_readReg, h.priv]
  have hpc := Sail.run_readReg_of_isInitialized s Register.PC h.init
  have hpr : runSail (prevent_reentrance Trig_Action.TA_Breakpoint Privilege.Machine) s =
      .ok (_get_Mstatus_MIE (s.regs.get Register.mstatus (h.init _)) == 0#1) s := by
    change runSail (do pure (_get_Mstatus_MIE (← LeanRV64D.readReg Register.mstatus) == 0#1)) s = _
    rw [Sail.run_readReg_bind_of_isInitialized s Register.mstatus h.init]
    rfl
  simp only [run_hart_active, LeanRV64D.SailME.run, pending_trigger_sp1,
    match_memory_trigger_before_sp1, pure_bind, bind_assoc,
    PreSail.PreSailME.run_lift_bind,
    runSail_bind, hcp, h.no_interrupt, hpc, hpr, h.fetched, hdec, hl,
    ext_fetch_hook, get_config_print_instr, Bool.false_eq_true, ite_false,
    Bool.false_and]
  simp only [Sail.run_writeReg]
  cases runSail (execute I)
      {s with regs := s.regs.insert Register.nextPC (BitVec.addInt (s.regs.get Register.PC (h.init _)) 4)} with
  | error error target => rfl
  | ok result target =>
    cases result <;> simp only [bind_assoc, pure_bind,
      PreSail.PreSailME.run_lift_bind, PreSail.PreSailME.run_pure]

/-- A satisfied `assert true` is a state-preserving no-op (`= pure ()`). -/
theorem run_assert_true (s : SailState) (msg : String) :
    (runSail ((PreSail.sail_assert true msg : SailM Unit))) s = .ok () s := rfl

/-! Machine mode with MIE clear cannot dispatch an interrupt, including hypervisor sources. -/

theorem run_getPendingSet_machine_none (s : SailState) (hs : s.isInitialized)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hs _)) = 0#1) :
    runSail (getPendingSet Privilege.Machine) s = .ok none s := by
  obtain ⟨enabledS, hS⟩ := RunPres.currentlyEnabled_S s hs
  obtain ⟨enabledH, hH⟩ : RunPres (currentlyEnabled .Ext_H) s := ⟨_, run_hypervisorEnabled s hs⟩
  obtain ⟨pending, hp⟩ := RunPres.readMipIncl s hs
  unfold getPendingSet
  cases enabledS <;> cases enabledH <;>
    simp only [run_bind_of_run s _ _ hS, run_bind_of_run s _ _ hH,
      Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc,
      Sail.run_readReg_bind_of_isInitialized s _ hs,
      run_bind_of_run s _ pending hp, andM, toBool, hmie,
      show (Privilege.Machine == Privilege.Machine) = true from rfl,
      show (Privilege.Machine == Privilege.Supervisor) = false from rfl,
      show (Privilege.Machine == Privilege.VirtualSupervisor) = false from rfl] <;> rfl

/-- **`dispatchInterrupt Machine = none`** (the `no_interrupt` field) from a quiescent-interrupt state. -/
theorem run_dispatchInterrupt_machine_none (s : SailState) (hinit : s.isInitialized)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hinit _)) = 0#1) :
    (runSail (dispatchInterrupt Privilege.Machine)) s = .ok none s := by
  unfold dispatchInterrupt
  rw [run_bind_of_run s _ none (run_getPendingSet_machine_none s hinit hmie)]
  rfl

/-! ## Stage 4 preamble — the `minstret_increment`-write frame

`try_step`'s first effect is `writeReg minstret_increment (← should_inc_minstret …)`, changing `s → s'`
BEFORE `run_hart_active` runs. Since `minstret_increment` is disjoint from every register the deep-field
reductions read (`mstatus`/`mideleg`/`PC`/`cur_privilege`/`hart_state`/`elp`/…) and the write leaves `s.mem`
untouched, every frame-stable precondition transfers to `s'` by `get`-on-disjoint-key — so the deep fields
re-derive on `s'` directly (the frame the earlier plan flagged as the crux, now dissolved by Stage 2'/3'
being precondition-parameterized). -/

/-- A CSR read is invariant under a write to the disjoint `minstret_increment` register. -/
theorem get_writeMinstret_ne {reg : Register} (h : Register.minstret_increment ≠ reg)
    (s : SailState) (v : RegisterType Register.minstret_increment) (hmem : reg ∈ s.regs)
    (hmem' : reg ∈ s.regs.insert Register.minstret_increment v) :
    (s.regs.insert Register.minstret_increment v).get reg hmem' = s.regs.get reg hmem := by
  rw [Std.ExtDHashMap.get_insert, dite_eq_right]
  simpa [beq_iff_eq] using h

/-- **`dispatchInterrupt Machine = none` survives the `minstret_increment` write** — the `no_interrupt`
field re-derives on the post-write state (Stage 2' is precondition-parameterized, all frame-stable). -/
theorem run_dispatchInterrupt_machine_none_writeMinstret (s : SailState) (hinit : s.isInitialized)
    (v : RegisterType Register.minstret_increment)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hinit _)) = 0#1) :
    (runSail (dispatchInterrupt Privilege.Machine)) {s with regs := s.regs.insert Register.minstret_increment v}
      = .ok none {s with regs := s.regs.insert Register.minstret_increment v} := by
  have hinit' : SailState.isInitialized {s with regs := s.regs.insert Register.minstret_increment v} :=
    SailState.isInitialized_insert s hinit _ _
  refine run_dispatchInterrupt_machine_none _ hinit' ?_
  rwa [get_writeMinstret_ne (by decide) s v (hinit _)]

/-- `isValidMemConfig` survives the `minstret_increment` write (all six config registers are disjoint). -/
theorem isValidMemConfig_writeMinstret (s : SailState) (hinit : s.isInitialized)
    (hconfig : SailMem.SailState.isValidMemConfig s hinit) (v : RegisterType Register.minstret_increment) :
    SailMem.SailState.isValidMemConfig {s with regs := s.regs.insert Register.minstret_increment v}
      (SailState.isInitialized_insert s hinit _ _) := by
  obtain ⟨h_cur, h_mprv, h_mseccfg, h_mseccfgpmm, h_htif, h_pma, h_pmp⟩ := hconfig
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [get_writeMinstret_ne (by decide) s v (hinit _)]
  exacts [h_cur, h_mprv, h_mseccfg, h_mseccfgpmm, h_htif, h_pma, h_pmp]

/-- **`fetch () = F_Base w` survives the `minstret_increment` write** — the `fetched` field re-derives on
the post-write state (Stage 3' is precondition-parameterized: `mem`/`PC`/config all frame-stable, the
align/`isRVC` preconditions are about `pc`/the word, untouched). -/
theorem run_fetch_eq_F_Base_writeMinstret
    (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (s : SailState) (hinit : s.isInitialized) (v : RegisterType Register.minstret_increment)
    (hconfig : SailMem.SailState.isValidMemConfig s hinit)
    (h_pc : s.regs.get Register.PC (hinit _) = pc)
    (h_access0 : BitVec.ofBool pc[0] = 0#1) (h_access1 : BitVec.ofBool pc[1] = 0#1)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0)
    (h_not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false)
    (hmem₀ : s.mem[(pc + 0).toNat]? = some data₀) (hmem₁ : s.mem[(pc + 0).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(pc + 0).toNat + 2]? = some data₂) (hmem₃ : s.mem[(pc + 0).toNat + 3]? = some data₃) :
    (runSail (fetch ())) {s with regs := s.regs.insert Register.minstret_increment v}
      = .ok (FetchResult.F_Base (data₃ ++ data₂ ++ data₁ ++ data₀))
          {s with regs := s.regs.insert Register.minstret_increment v} :=
  SailMem.run_fetch_eq_F_Base_of_isInitialized pc data₀ data₁ data₂ data₃ _
    (SailState.isInitialized_insert s hinit _ _)
    (isValidMemConfig_writeMinstret s hinit hconfig v)
    (by rwa [get_writeMinstret_ne (by decide) s v (hinit _)])
    h_access0 h_access1 h_aligned h_in_range h_align h_not_rvc hmem₀ hmem₁ hmem₂ hmem₃

/-! ## Stage 4 — the `try_step` outer-frame reduction -/

set_option linter.unusedVariables false in
/-- **`try_step step_no false` reduces to the `tick_pc` + minstret-bump tail** on the post-`run_hart_active`
state `s''`, given a successful active-hart step (`h_ha`: `run_hart_active` yields `Retire_Success`). The
outer frame peels: `ext_pre_step_hook` (no-op) → `should_inc_minstret` (`b`) → `writeReg minstret_increment`
(`s'`) → `hart_state` dispatch → `run_hart_active` (`h_ha`) → the `Retire_Success` `assert` (true) → the
`HART_ACTIVE` tail (`tick_pc`, the retired-gated minstret bump, dead rvfi/hooks). -/
theorem tryStep_eq_of_hart_active (source s : SailState) (step_no : Nat)
    (b : Bool) (ib : instr_info) (s'' : SailState)
    (prepared : runSail (update_mip ()) source = .ok () s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hb : (runSail (should_inc_minstret Privilege.Machine)) s = .ok b s)
    (hcp : (runSail (LeanRV64D.readReg Register.cur_privilege)) s = .ok Privilege.Machine s)
    (h_ha : (runSail (run_hart_active step_no)) {s with regs := s.regs.insert Register.minstret_increment b}
      = .ok (Step.Step_Execute (ExecutionResult.Retire_Success (), ib)) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (runSail (try_step step_no false)) source
      = (runSail (do
          tick_pc ()
          let mi ← LeanRV64D.readReg Register.minstret_increment
          if (true && mi) = true then do
              let m ← LeanRV64D.readReg Register.minstret
              LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
              clear_written_event_index ()
              (pure false : SailM Bool)
            else do
              clear_written_event_index ()
              (pure false : SailM Bool))) s'' := by
  unfold try_step
  rw [run_bind_of_run' source s _ () prepared]
  rw [run_bind_of_run s _ Privilege.Machine hcp, run_bind_of_run s _ b hb, run_writeReg_bind]
  have hhs' : (runSail (LeanRV64D.readReg Register.hart_state))
      {s with regs := s.regs.insert Register.minstret_increment b}
      = .ok (HartState.HART_ACTIVE ()) {s with regs := s.regs.insert Register.minstret_increment b} := by
    rw [Sail.run_readReg, show ({s with regs := s.regs.insert Register.minstret_increment b} :
      SailState).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) from hactive]
  rw [bind_assoc, run_bind_of_run _ _ (HartState.HART_ACTIVE ()) hhs',
    run_bind_of_run' _ s'' (run_hart_active step_no) _ h_ha]
  have hhs'' : (runSail (LeanRV64D.readReg Register.hart_state)) s'' = .ok (HartState.HART_ACTIVE ()) s'' := by
    rw [Sail.run_readReg, show s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) from h_active'']
  simp only [match_icount_triggers_sp1]
  simp only [dispatch_events, update_triggers_sp1, get_config_rvfi_eq, Bool.false_eq_true, ite_false, pure_bind,
    bind_assoc, andM, toBool, Bool.true_and]
  simp only [run_bind_of_run s'' _ (HartState.HART_ACTIVE ()) hhs'', hart_is_active_active,
    run_bind_of_run s'' _ () (run_assert_true s'' _)]

end SP1Clean.TryStepReduction
