import SP1Clean.Model.Semantics.SailFetch

/-! # Normal retirement and its complete Sail bookkeeping effects

These circuit-independent lemmas compose an actual execute-stage result with official `try_step`.
They preserve initialization and expose PC, GPR, memory, other-register, runtime, and retirement
observations. Instruction-family frame laws supply the execute-stage result separately.
-/

open LeanRV64D
namespace SP1Clean.Advance

open SP1Clean Sail Sail.ArchSem LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.SailMem

/-! ## The generic composition -/

/-- **`run_hart_active` reaches the `Retire_Success` step**, given the execute stage lands there: from the
Phase-3 ladder (`run_hart_active_eq_of_ready`) + a `hstage` fact that `writeReg nextPC (PC+4); execute I`
runs to `Retire_Success` at `s''`, `run_hart_active` yields `Step_Execute (Retire_Success, …)` at `s''`.
The `ExecuteAs` redirect is dead (`execute I` returned `Retire_Success`, not `ExecuteAs`). -/
theorem run_hart_active_reaches (s' s_a s'' : SailState) (w : BitVec 32) (I : instruction) (step_no : Nat)
    (hslr : StraightLineReady s' w)
    (hdec : (runSail (ext_decode w)) s' = .ok I s')
    (hsa : (runSail (LeanRV64D.writeReg Register.nextPC
        (BitVec.addInt (s'.regs.get Register.PC (hslr.init Register.PC)) 4))) s' = .ok () s_a)
    (hexec : (runSail (execute I)) s_a = .ok (ExecutionResult.Retire_Success ()) s'') :
    (runSail (run_hart_active step_no)) s'
      = .ok (Step.Step_Execute (ExecutionResult.Retire_Success (), {
          fetch_privilege := .Machine,
          fetch_trigger_reentrance := _get_Mstatus_MIE (s'.regs.get Register.mstatus (hslr.init _)) == 0#1,
          fetched_instruction := I, executed_instruction := some I,
          instbits := zero_extend (m := 32) w, compressed := false })) s'' := by
  rw [run_hart_active_eq_of_ready s' w I step_no hslr hdec]
  rw [run_bind_of_run s' _ _ (Sail.run_readReg_of_isInitialized s' Register.PC hslr.init),
    run_bind_of_run' s' s_a _ () hsa,
    run_bind_of_run' s_a s'' (execute I) (ExecutionResult.Retire_Success ()) hexec]
  rfl

/-- **`try_step` reaches the row's execute effect** — the full outer-frame composition. On the
post-minstret-write state `s' = {s with regs.insert minstret_increment b}` (with `StraightLineReady s'`),
`try_step 0 false` reduces to its `tick_pc` + minstret tail on `s''` (= the post-`execute I` state), via
`run_hart_active_reaches` (into `h_ha`) + `tryStep_eq_of_hart_active`. -/
theorem tryStep_reaches (source s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (prepared : runSail (update_mip ()) source = .ok () s)
    (hb : (runSail (should_inc_minstret Privilege.Machine)) s = .ok b s)
    (hcp : (runSail (LeanRV64D.readReg Register.cur_privilege)) s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (runSail (ext_decode w)) ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (runSail (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)))
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (runSail (execute I)) s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())) :
    (runSail (try_step 0 false)) source
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
              (pure false : SailM Bool))) s'' :=
  tryStep_eq_of_hart_active source s 0 b _ s'' prepared hactive hb hcp
    (run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec) h_active''

/-- **The minstret-bump tail is a register-file frame**: run on any initialized state `t`, the
`minstret_increment`-gated `minstret ← minstret+1` bump yields `.ok false t'` with `t'` agreeing with `t`
on `PC` and on the whole `BitVec 5` register file — retirement touches `minstret` and clears `written_event_index`. -/
theorem minstret_tail_effect (t : SailState) (hinit : t.isInitialized) :
    ∃ t' : SailState,
      (runSail (do
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            clear_written_event_index ()
            (pure false : SailM Bool)
          else do
            clear_written_event_index ()
            (pure false : SailM Bool))) t = .ok false t'
      ∧ t'.regs.get? Register.PC = t.regs.get? Register.PC
      ∧ (∀ idx : BitVec 5, t'.get_reg? idx = t.get_reg? idx)
      ∧ t'.mem = t.mem
      ∧ (∀ R : Register, R ≠ Register.minstret → R ≠ Register.written_event_index → t'.regs.get? R = t.regs.get? R)
      ∧ t'.isInitialized
      ∧ t'.cycleCount = t.cycleCount ∧ t'.sailOutput = t.sailOutput
      ∧ t'.regs.get? Register.minstret =
        (t.regs.get? Register.minstret).map (fun value =>
          if (true && t.regs.get Register.minstret_increment (hinit _)) = true
          then BitVec.addInt value 1 else value)
      ∧ t'.regs.get? Register.written_event_index = some none := by
  rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret_increment hinit)]
  split
  · rw [run_bind_of_run t _ _ (Sail.run_readReg_of_isInitialized t Register.minstret hinit),
      run_writeReg_bind]
    simp only [clear_written_event_index, run_writeReg_bind]
    refine ⟨_, rfl, ?_, (fun idx => ?_), rfl, (fun R hR hW => ?_),
      SailState.isInitialized_insert _ (SailState.isInitialized_insert t hinit _ _) _ _, rfl, rfl, ?_, by rw [Std.ExtDHashMap.get?_insert_self]⟩
    · simp only [Std.ExtDHashMap.get?_insert, show (Register.written_event_index == Register.PC) = false from rfl,
        show (Register.minstret == Register.PC) = false from rfl, Bool.false_eq_true, ↓reduceDIte]
    · rw [SailState.get_reg?_insert_of_ne
        (s := {t with
          regs := t.regs.insert Register.minstret (BitVec.addInt (t.regs.get Register.minstret (hinit _)) 1)})
        (reg := Register.written_event_index) (by unfold reg_idx_to_Register; split <;> decide)]
      exact SailState.get_reg?_insert_of_ne (by unfold reg_idx_to_Register; split <;> decide)
    · rw [Std.ExtDHashMap.get?_insert, dite_eq_right (fun hc => hW (beq_iff_eq.mp hc).symm),
        Std.ExtDHashMap.get?_insert, dite_eq_right (fun hc => hR (beq_iff_eq.mp hc).symm)]
    · rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide),
        Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit _)]
      simp only [Option.map_some]
  · simp only [clear_written_event_index, run_writeReg_bind]
    refine ⟨_, rfl, ?_, (fun idx => ?_), rfl, (fun R _ hW => ?_),
      SailState.isInitialized_insert t hinit _ _, rfl, rfl, ?_, by rw [Std.ExtDHashMap.get?_insert_self]⟩
    · rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide)]
    · exact SailState.get_reg?_insert_of_ne (by unfold reg_idx_to_Register; split <;> decide)
    · rw [Std.ExtDHashMap.get?_insert, dite_eq_right (fun hc => hW (beq_iff_eq.mp hc).symm)]
    · rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide), Std.ExtDHashMap.get?_eq_some_get (hinit _)]
      simp only [Option.map_some]

/-- **The `tick_pc` + minstret tail's effect** on the observables: it commits `PC ← nextPC` and leaves every
`BitVec 5` register file entry fixed (the minstret bump touches only the `minstret` CSR, `tick_pc` only
`PC` — both outside the register file). -/
theorem tail_bookkeeping (s'' : SailState) (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState,
      (runSail (do
        tick_pc ()
        let mi ← LeanRV64D.readReg Register.minstret_increment
        if (true && mi) = true then do
            let m ← LeanRV64D.readReg Register.minstret
            LeanRV64D.writeReg Register.minstret (BitVec.addInt m 1)
            clear_written_event_index ()
            (pure false : SailM Bool)
          else do
            clear_written_event_index ()
            (pure false : SailM Bool))) s'' = .ok false s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret → R ≠ Register.written_event_index →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized
      ∧ s_final.cycleCount = s''.cycleCount ∧ s_final.sailOutput = s''.sailOutput
      ∧ s_final.regs.get? Register.minstret =
        (s''.regs.get? Register.minstret).map (fun value =>
          if (true && s''.regs.get Register.minstret_increment (hinit'' _)) = true
          then BitVec.addInt value 1 else value)
      ∧ s_final.regs.get? Register.written_event_index = some none := by
  have ticked : runSail (tick_pc ()) s'' = .ok ()
      {s'' with regs := s''.regs.insert Register.PC (s''.regs.get Register.nextPC (hinit'' _))} := by
    rw [Sail.run_tick_pc, Sail.run_readReg_bind_of_isInitialized s'' Register.nextPC hinit'', Sail.run_writeReg]
  rw [run_bind_of_run' _ _ _ () ticked]
  obtain ⟨t', hrun, hPC', hxreg', hmem', hframe', hinit', cycles, output, retired, cleared⟩ := minstret_tail_effect
    {s'' with regs := s''.regs.insert Register.PC (s''.regs.get Register.nextPC (hinit'' _))}
    (SailState.isInitialized_insert s'' hinit'' _ _)
  refine ⟨t', hrun, ?_, (fun idx => ?_), hmem', (fun R hRpc hRm hRw => ?_), hinit', cycles, output, ?_, cleared⟩
  · rw [hPC', Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_eq_some_get (hinit'' _)]
  · rw [hxreg' idx]; exact SailState.get_reg?_insert_PC
  · rw [hframe' R hRm hRw, Std.ExtDHashMap.get?_insert, dite_eq_right (fun hc => hRpc (beq_iff_eq.mp hc).symm)]
  · simpa only [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get_insert,
      show (Register.PC == Register.minstret_increment) = false from rfl,
      show (Register.PC == Register.minstret) = false from rfl,
      Bool.false_eq_true, ↓reduceDIte] using retired

/-- **The core `SailStep` composition** — joins the landed ladder (`tryStep_reaches`) with the tail's
observable effect (`tail_bookkeeping`). Given the ladder inputs on the post-minstret-write state, `try_step`
takes one real step to some `s_final` whose `PC` is the post-execute `nextPC` and whose `BitVec 5`
register file agrees with the post-execute state `s''`. This is the whole `try_step`-side content of a
register-writing chip's `advance`; per-chip work is only characterizing `s''` (via the execute bridge)
and building the ladder inputs from `RefinesAt`/`OperandsBound`. -/
theorem sailStep_of_ladder_bookkeeping (source s s_a s'' : SailState) (w : BitVec 32) (I : instruction) (b : Bool)
    (prepared : runSail (update_mip ()) source = .ok () s)
    (hb : (runSail (should_inc_minstret Privilege.Machine)) s = .ok b s)
    (hcp : (runSail (LeanRV64D.readReg Register.cur_privilege)) s = .ok Privilege.Machine s)
    (hactive : (s.regs.insert Register.minstret_increment b).get? Register.hart_state
      = some (HartState.HART_ACTIVE ()))
    (hslr : StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b}) w)
    (hdec : (runSail (ext_decode w)) ({s with regs := s.regs.insert Register.minstret_increment b})
      = .ok I ({s with regs := s.regs.insert Register.minstret_increment b}))
    (hsa : (runSail (LeanRV64D.writeReg Register.nextPC (BitVec.addInt
        ((s.regs.insert Register.minstret_increment b).get Register.PC (hslr.init Register.PC)) 4)))
        ({s with regs := s.regs.insert Register.minstret_increment b}) = .ok () s_a)
    (hexec : (runSail (execute I)) s_a = .ok (ExecutionResult.Retire_Success ()) s'')
    (h_active'' : s''.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hinit'' : s''.isInitialized) :
    ∃ s_final : SailState, (runSail (try_step 0 false)) source = .ok false s_final
      ∧ SailRetiresNormally source s_final
      ∧ s_final.regs.get? Register.PC = s''.regs.get? Register.nextPC
      ∧ (∀ idx : BitVec 5, s_final.get_reg? idx = s''.get_reg? idx)
      ∧ s_final.mem = s''.mem
      ∧ (∀ R : Register, R ≠ Register.PC → R ≠ Register.minstret → R ≠ Register.written_event_index →
          s_final.regs.get? R = s''.regs.get? R)
      ∧ s_final.isInitialized
      ∧ s_final.cycleCount = s''.cycleCount ∧ s_final.sailOutput = s''.sailOutput
      ∧ s_final.regs.get? Register.minstret =
        (s''.regs.get? Register.minstret).map (fun value =>
          if (true && s''.regs.get Register.minstret_increment (hinit'' _)) = true
          then BitVec.addInt value 1 else value)
      ∧ s_final.regs.get? Register.written_event_index = some none := by
  obtain ⟨s_final, hrun, hPC, hxreg, hmem, hframe, hinitf, cycles, output, retired, cleared⟩ := tail_bookkeeping s'' hinit''
  have hstep : (runSail (try_step 0 false)) source = .ok false s_final := by
    rw [tryStep_reaches source s s_a s'' w I b prepared hb hcp hactive hslr hdec hsa hexec h_active'']
    exact hrun
  refine ⟨s_final, hstep, ?_, hPC, hxreg, hmem, hframe, hinitf, cycles, output, retired, cleared⟩
  exact ⟨s, prepared, b, _, s'', hb,
    run_hart_active_reaches _ s_a s'' w I 0 hslr hdec hsa hexec, hstep⟩

end SP1Clean.Advance
