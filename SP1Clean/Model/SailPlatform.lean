import SP1Clean.Model.SailWrap
import Mathlib.Tactic.IntervalCases

/-! # Sail platform reads and per-step bookkeeping

State-preserving platform queries and the exact interrupt-register update performed by the
upstream step function. The proofs observe ArchSem's sequential interpreter directly.
-/

namespace SP1Clean.TryStepReduction
open Sail Sail.ArchSem LeanRV64D LeanRV64D.Functions

/-- A successful state-preserving action supplies its value to the remaining interpreted action. -/
theorem run_bind_of_run {α β : Type} (s : SailState) (m : SailM α) (x : α)
    (hm : (runSail m) s = .ok x s) (k : α → SailM β) : (runSail (m >>= k)) s = (runSail (k x)) s := by
  simp only [runSail_bind, hm]

/-- A successful state-changing action supplies its value and final state to the continuation. -/
theorem run_bind_of_run' {α β : Type} (s s' : SailState) (m : SailM α) (x : α)
    (hm : (runSail m) s = .ok x s') (k : α → SailM β) : (runSail (m >>= k)) s = (runSail (k x)) s' := by
  simp only [runSail_bind, hm]

/-- **`RunPres m s`**: `m` runs to `.ok _ s` — a read-only, state-preserving `SailM` action at `s`. -/
def RunPres {α : Type} (m : SailM α) (s : SailState) : Prop := ∃ v, (runSail m) s = .ok v s

theorem RunPres.pure {α : Type} (x : α) (s : SailState) : RunPres (Pure.pure x) s := ⟨x, rfl⟩

theorem RunPres.readReg (s : SailState) (reg : Register) (hs : s.isInitialized) :
    RunPres (LeanRV64D.readReg reg) s := ⟨_, Sail.run_readReg_of_isInitialized s reg hs⟩

theorem RunPres.bind {α β : Type} {m : SailM α} {k : α → SailM β} {s : SailState}
    (hm : RunPres m s) (hk : ∀ v, RunPres (k v) s) : RunPres (m >>= k) s := by
  obtain ⟨v, hv⟩ := hm
  obtain ⟨w, hw⟩ := hk v
  exact ⟨w, by rwa [run_bind_of_run s m v hv]⟩

theorem RunPres.ite {α : Type} {c : Prop} [Decidable c] {a b : SailM α} {s : SailState}
    (ha : RunPres a s) (hb : RunPres b s) : RunPres (if c then a else b) s := by
  by_cases h : c <;> simp only [h, ite_true, ite_false] <;> [exact ha; exact hb]

/-- `currentlyEnabled Ext_Zicsr` is state-preserving (a `pure`, no register read). -/
theorem RunPres.currentlyEnabled_Zicsr (s : SailState) :
    RunPres (currentlyEnabled extension.Ext_Zicsr) s := by
  unfold currentlyEnabled; exact ⟨_, rfl⟩

/-- `currentlyEnabled Ext_S` is state-preserving (reads `misa`, recurses to the `pure` `Zicsr`). -/
theorem RunPres.currentlyEnabled_S (s : SailState) (hs : s.isInitialized) :
    RunPres (currentlyEnabled extension.Ext_S) s := by
  simp only [currentlyEnabled, hartSupports, andM, toBool, pure_bind]
  apply RunPres.bind (RunPres.readReg s Register.misa hs)
  intro value
  split <;> exact RunPres.pure _ s


/-- Every interrupt class is supported by this platform, so its mask is the identity. -/
theorem supported_interrupts_mask_sp1 (bits : BitVec 64) : supported_interrupts_mask bits = (pure bits : SailM _) := by
  simp only [supported_interrupts_mask, currentlyEnabled, hartSupports, andM, toBool, pure_bind]
  change pure ((BitVec.allOnes 64) &&& bits) = pure bits
  rw [BitVec.allOnes_and]

/-- The ISA bits on which the generated hypervisor-enable query depends. -/
def hypervisorEnabled (misa : BitVec 64) : Bool :=
  (_get_Misa_H misa == 1#1) && ((_get_Misa_I misa == 1#1) && (_get_Misa_S misa == 1#1))

/-- The data-only ISA query agrees with the upstream interpreter. -/
theorem run_hypervisorEnabled (s : SailState) (hs : s.isInitialized) :
    runSail (currentlyEnabled .Ext_H) s = .ok (hypervisorEnabled (s.regs.get Register.misa (hs _))) s := by
  simp only [currentlyEnabled, hartSupports, andM, orM, toBool, pure_bind, bind_assoc,
    Sail.run_readReg_bind_of_isInitialized s _ hs]
  unfold hypervisorEnabled
  cases h : (_get_Misa_H (s.regs.get Register.misa (hs _)) == 1#1) <;>
    cases i : (_get_Misa_I (s.regs.get Register.misa (hs _)) == 1#1) <;>
    cases ss : (_get_Misa_S (s.regs.get Register.misa (hs _)) == 1#1) <;>
    simp only [i, ss, show (Functions.xlen == 64) = true from rfl, pure_bind,
      Sail.run_readReg_bind_of_isInitialized s _ hs, runSail_pure,
      Bool.false_and, Bool.true_and]

/-- The platform clears software interrupts and refreshes hypervisor injection when enabled. -/
def refreshedMipBits (isa injected pending : BitVec 64) : BitVec 64 :=
  let pending := Sail.BitVec.updateSubrange pending 3 3 0#1
  if hypervisorEnabled isa then
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange pending 10 10 (_get_Minterrupts_VSEI injected)) 6 6
      (_get_Minterrupts_VSTI injected)
  else pending

/-- Observe the interrupt value after one refresh. Missing keys use a total fallback; execution
agreement below requires initialization. This does not execute an instruction. -/
def refreshedMip (state : SailState) : BitVec 64 :=
  refreshedMipBits ((state.regs.get? .misa).getD 0) ((state.regs.get? .hvip).getD 0)
    ((state.regs.get? .mip).getD 0)

/-- Repeated refreshes have the same value while ISA and injected interrupts remain fixed. -/
theorem refreshedMipBits_idempotent (isa injected pending : BitVec 64) :
    refreshedMipBits isa injected (refreshedMipBits isa injected pending) =
      refreshedMipBits isa injected pending := by
  unfold refreshedMipBits
  cases hypervisorEnabled isa <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    ext i
    interval_cases i <;> simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

/-- With no interrupt generator, reading pending interrupts only observes the register file. -/
theorem RunPres.readMipIncl (s : SailState) (hs : s.isInitialized) :
    RunPres (read_mip XipReadType.IncludePlatformInterrupts) s := by
  simp only [read_mip, external_interrupts_pending, supervisor_software_interrupt_pending,
    plat_have_sig, Bool.false_eq_true, ite_false, pure_bind]
  apply RunPres.bind (RunPres.readReg s Register.hgeie hs)
  intro _
  apply RunPres.bind (RunPres.currentlyEnabled_S s hs)
  intro enabled
  cases enabled <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    rw [supported_interrupts_mask_sp1, pure_bind]
    exact RunPres.bind (RunPres.readReg s Register.mip hs) (fun _ => RunPres.pure _ s)

private theorem readHenvcfg (s : SailState) (hs : s.isInitialized) :
    RunPres (read_henvcfg ()) s := by
  unfold read_henvcfg
  repeat' first
  | exact RunPres.readReg s _ hs
  | exact RunPres.pure _ s
  | apply RunPres.bind
  | intro value

private theorem finishMip (s : SailState) (hs : s.isInitialized) (old bits : BitVec 64) :
    runSail (do
      let value ← supported_interrupts_mask bits
      LeanRV64D.writeReg Register.mip value
      let actual ← LeanRV64D.readReg Register.mip
      if (old != actual) = true then
        csr_name_write_callback "mip" (← read_mip XipReadType.IncludePlatformInterrupts)
      else pure ()) s = .ok () {s with regs := s.regs.insert Register.mip bits} := by
  rw [supported_interrupts_mask_sp1, pure_bind, Sail.run_writeReg_bind]
  simp only [LeanRV64D.readReg, runSail_bind, Sail.run_readReg, Std.ExtDHashMap.get?_insert_self]
  split
  · obtain ⟨observed, ho⟩ := RunPres.readMipIncl
      {s with regs := s.regs.insert Register.mip bits} (s.isInitialized_insert hs _ _)
    simp only [runSail_bind] at ho ⊢
    rw [ho]
    rfl
  · rfl

/-- The exact upstream refresh changes only `mip` and agrees with the data observation. -/
theorem run_update_mip (s : SailState) (hs : s.isInitialized) :
    runSail (update_mip ()) s = .ok () {s with regs := s.regs.insert .mip (refreshedMip s)} := by
  have observations : ∀ reg, s.regs.get? reg = some (s.regs.get reg (hs reg)) :=
    fun reg => Std.ExtDHashMap.get?_eq_some_get (hs reg)
  simp only [refreshedMip, observations, Option.getD_some, refreshedMipBits]
  simp only [update_mip, get_mtime, get_hart_mtimecmp, machine_software_interrupt_pending,
    plat_have_clint, plat_have_sig, Bool.false_eq_true, ite_false, pure_bind, bind_assoc,
    Sail.run_readReg_bind_of_isInitialized s _ hs]
  rw [run_bind_of_run s _ _ (run_hypervisorEnabled s hs)]
  cases enabled : hypervisorEnabled (s.regs.get .misa (hs _)) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind]
  · exact finishMip s hs _ _
  · obtain ⟨henv, hh⟩ := readHenvcfg s hs
    simp only [bind_assoc, Sail.run_readReg_bind_of_isInitialized s _ hs,
      currentlyEnabled, hartSupports, andM, toBool, pure_bind]
    rw [run_bind_of_run s _ henv hh]
    simp only [Bool.and_false, pure_bind, Bool.false_eq_true, ite_false, BitVec.or_zero]
    exact finishMip s hs _ _

theorem match_memory_trigger_before_sp1 (priv : Privilege) (payload : MemoryTriggerPayload) :
    match_memory_trigger_before priv payload = (pure none : SailM _) := by
  simp [match_memory_trigger_before, currentlyEnabled, hartSupports, LeanRV64D.not]

theorem match_memory_trigger_after_sp1 (priv : Privilege) (payload : MemoryTriggerPayload) :
    match_memory_trigger_after priv payload = (pure () : SailM Unit) := by
  simp [match_memory_trigger_after, currentlyEnabled, hartSupports, LeanRV64D.not]

/-- Unsupported trigger retirement does not inspect trigger bookkeeping. -/
theorem update_triggers_sp1 : update_triggers () = (pure () : SailM Unit) := by
  simp [update_triggers, currentlyEnabled, hartSupports, LeanRV64D.not]

/-- Unsupported instruction-count triggers cannot alter retirement. -/
theorem match_icount_triggers_sp1 (priv : Privilege) (reentrant : Bool) :
    match_icount_triggers priv reentrant = (pure () : SailM Unit) := by
  simp [match_icount_triggers, currentlyEnabled, hartSupports, LeanRV64D.not]

/-- Unsupported pending triggers cannot intercept an instruction. -/
theorem pending_trigger_sp1 (priv : Privilege) :
    find_highest_priority_pending_trigger priv = (pure none : SailM _) := by
  simp [find_highest_priority_pending_trigger, currentlyEnabled, hartSupports, LeanRV64D.not]

end SP1Clean.TryStepReduction
