import SP1Clean.Model.Semantics.SailReadOnly

/-! # Read-only stages of ordinary Sail memory accesses

Physical checks, split loads and effective-address checks preserve the complete state, including
fault results. The split loop is handled at arbitrary fuel, without assuming aligned addresses.
-/

namespace SP1Clean.SailMem
open Sail Sail.ArchSem LeanRV64D LeanRV64D LeanRV64D.Functions
open SP1Clean.SailFrame SP1Clean.Soundness.Target SP1Clean.TryStepReduction

private theorem readOnly_readByte (source : SailState) (address : ℕ) :
    ∀ value target, (Sail.ArchSem.readByte address : ArchSemSeqM exception _).run source =
      .ok value target → target = source := by
  intro value target ran
  cases found : source.mem[address]? with
  | some byte =>
    rw [run_readByte address byte source found] at ran
    cases ran
    rfl
  | none =>
    have absent : source.mem.get? address = none := found
    simp only [Sail.ArchSem.readByte, bind, EStateM.bind, EStateM.run,
      getThe, MonadStateOf.get, MonadState.get, get, EStateM.get, absent] at ran
    cases ran

private theorem seq_bind_frame {α β : Type} {source : SailState}
    (action : ArchSemSeqM exception α) (next : α → ArchSemSeqM exception β)
    (first : ∀ value target, action.run source = .ok value target → target = source)
    (rest : ∀ value result target, (next value).run source = .ok result target → target = source) :
    ∀ result target, (action >>= next).run source = .ok result target → target = source := by
  intro result target ran
  have actual : EStateM.bind action next source = .ok result target := ran
  cases h : action source with
  | error error middle =>
    simp only [EStateM.bind, h] at actual
    cases actual
  | ok value middle =>
    have same := first value middle h
    subst middle
    simp only [EStateM.bind, h] at actual
    exact rest value result target actual

private theorem readOnly_readBytes (source : SailState) (width address : ℕ) :
    ∀ value target, (Sail.ArchSem.readBytes width address : ArchSemSeqM exception _).run source =
      .ok value target → target = source := by
  induction width generalizing address with
  | zero => intro value target ran; cases ran; rfl
  | succ width ih =>
    cases width with
    | zero =>
      apply seq_bind_frame _ _ (readOnly_readByte source address)
      intro value result target ran
      cases ran
      rfl
    | succ width =>
      apply seq_bind_frame _ _ (readOnly_readByte source address)
      intro byte
      apply seq_bind_frame _ _ (ih (address + 1))
      intro bytes result target ran
      cases ran
      rfl

/-- A physical RAM read either fails or leaves the entire state unchanged. -/
theorem readOnly_read_ram (source : SailState) (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (read_ram read_kind.Read_plain access address width false) := by
  rcases address with ⟨address⟩
  unfold read_ram
  simp only [pure_bind, Bool.false_eq_true, ite_false]
  intro value target ran
  unfold runSail at ran
  rw [interpretSailEffects_bind] at ran
  simp only [LeanRV64D.ArchSem.sail_mem_read, PreSail.sail_mem_read, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect, Mem_request.toArchSem,
    show (0 != (0 : Nat)) = false from rfl, Function.comp_apply,
    Bool.false_eq_true, ite_false, pure_bind, bind_assoc] at ran
  apply seq_bind_frame _ _ (readOnly_readBytes source width address.toNat) _ value target ran
  intro bytes result target ran
  cases ran
  rfl

private theorem readOnly_assert (source : SailState) (condition : Bool) (message : String) :
    ReadOnlyAt source (PreSail.sail_assert condition message) := by
  cases condition
  · exact ReadOnlyAt.throw source _
  · exact ReadOnlyAt.pure source _

/-- Splitting chooses sizes and checks arithmetic; it does not modify the machine. -/
theorem readOnly_split_misaligned (source : SailState) (address : physaddr) (width granule : ℕ)
    (splittable : Splittability) :
    ReadOnlyAt source (split_misaligned address width granule splittable) := by
  rcases address with ⟨address⟩
  simp only [split_misaligned]
  split
  · exact ReadOnlyAt.pure source _
  · change ReadOnlyAt source (split_access address width)
    exact (readOnly_assert source _ _).bind fun _ => ReadOnlyAt.pure source _

private theorem readOnly_mag (source : SailState) (address : physaddr) (width : ℕ)
    (attributes : PMA) (store : Bool) :
    ReadOnlyAt source (mag_pma_check attributes
      (if store then .Store .Data else .Load .Data) address width) := by
  cases store <;> simp only [Bool.false_eq_true, ↓reduceIte, mag_pma_check,
    is_mag_applicable_access, pure_bind]
  all_goals
    split
    · exact ReadOnlyAt.pure source _
    · simp only [pma_misaligned_exception, pure_bind]
      split
      · exact ReadOnlyAt.pure source _
      · split <;> exact ReadOnlyAt.pure source _

private theorem readOnly_pma (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) (store : Bool) :
    ReadOnlyAt source (pmaCheck address width (if store then .Store .Data else .Load .Data)
      .PBMT_PMA false) := by
  unfold pmaCheck
  apply ReadOnlyEAt.runE
  apply ReadOnlyEAt.bindE
  · apply ReadOnlyEAt.bindE
    · exact (ReadOnlyAt.of_run (Sail.run_readReg_of_isInitialized source _ cfg.init)).lift
    · intro regions
      split
      · cases store <;> exact ReadOnlyEAt.earlyReturn source _
      · exact ReadOnlyEAt.pure source _
  · intro attributes
    have mag := readOnly_mag source address width attributes store
    cases store <;>
      simp only [Bool.false_eq_true, ↓reduceIte, LeanRV64D.not, Bool.not_false]
    all_goals
      apply ReadOnlyEAt.bindE (ReadOnlyEAt.pure source _)
      intro canAccess
      split
      · exact ReadOnlyEAt.pure source _
      · apply ReadOnlyEAt.bindE
        · exact mag.lift
        · intro result
          rcases result with (⟨splittable, granule⟩ | error)
          · exact ReadOnlyEAt.pure source _
          · cases error <;> exact ReadOnlyEAt.pure source _

/-- PMP priority and PMA lookup preserve state for both ordinary data-access directions. -/
theorem readOnly_check_pma (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) (store : Bool) :
    ReadOnlyAt source (check_pma_with_pmp_priority
      (if store then .Store .Data else .Load .Data) .PBMT_PMA .Machine address width false) := by
  unfold check_pma_with_pmp_priority
  apply (readOnly_pma source cfg address width store).bind
  intro result
  cases result
  · exact ReadOnlyAt.pure source _
  · apply (ReadOnlyAt.of_run (run_pmpCheck_none address width _ source cfg.init
      cfg.toValidMemConfig.h_pmp_off)).bind
    intro result
    cases result <;> exact ReadOnlyAt.pure source _

/-- MMIO is absent at every physical address in the configured platform. -/
theorem run_mmio_readable_false (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    (runSail (within_mmio_readable address width)) source = .ok false source := by
  rcases address with ⟨address⟩
  have ran := run_within_mmio_readable_mmio address 0 width source cfg.init cfg.toValidMemConfig.h_htif_disabled
  change (runSail (within_mmio_readable (.Physaddr (address + 0#64 + 0#64)) width)) source = _ at ran
  have zero : ∀ a : BitVec 64, a + 0#64 = a := BitVec.add_zero
  simpa only [zero] using ran

/-- A checked load preserves all state even when the physical access is split or faults. -/
theorem readOnly_checked_mem_read (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (checked_mem_read (.Load .Data) .PBMT_PMA .Machine address width
      false false false false) := by
  unfold checked_mem_read
  apply ReadOnlyEAt.runE
  apply ReadOnlyEAt.bindE
  · apply (readOnly_check_pma source cfg address width false).lift.bindE
    intro result
    cases result
    · exact ReadOnlyEAt.pure source _
    · exact ReadOnlyEAt.earlyReturn source _
  · rintro ⟨splittable, granule⟩
    apply (readOnly_split_misaligned source address width granule splittable).lift.bindE
    rintro ⟨count, size⟩
    apply ReadOnlyEAt.bindE_of_run (show (runSail (read_kind_of_flags false false false)) source =
      .ok read_kind.Read_plain source from rfl)
    apply ReadOnlyEAt.bindE
    · apply ReadOnlyEAt.bindE
      · apply ReadOnlyEAt.untilE
        · intro value
          exact ReadOnlyEAt.pure source _
        · rintro ⟨data, finished, index⟩
          apply ReadOnlyEAt.bindE_of_run (show (runSail (PreSail.sail_assert true "loop dummy assert")) source =
            .ok () source from rfl)
          apply ReadOnlyEAt.bindE_of_run (run_pmpCheck_none _ _ _ source cfg.init cfg.toValidMemConfig.h_pmp_off)
          apply ReadOnlyEAt.bindE_of_run (run_mmio_readable_false source cfg _ _)
          apply ReadOnlyEAt.bindE
          · apply (readOnly_read_ram source _ _ _).lift.bindE
            rintro ⟨data, metadata⟩
            exact ReadOnlyEAt.pure source _
          · intro data
            exact ReadOnlyEAt.pure source _
      · intro value
        exact ReadOnlyEAt.pure source _
    · intro value
      exact ReadOnlyEAt.pure source _

/-- The complete physical load path, including callbacks and split accesses, is read-only. -/
theorem readOnly_mem_read (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (mem_read (.Load .Data) .PBMT_PMA .Machine address width false false false) := by
  unfold mem_read mem_read_priv_meta
  exact ((readOnly_checked_mem_read source cfg address width).bind
    fun _ => ReadOnlyAt.pure source _).bind fun _ => ReadOnlyAt.pure source _

/-- MMIO writes are absent at every physical address in the configured platform. -/
theorem run_mmio_writable_false (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    runSail (within_mmio_writable address width) source = .ok false source := by
  rcases address with ⟨address⟩
  have ran := run_within_mmio_writable_mmio address 0 width source cfg.init cfg.htif_disabled
  change runSail (within_mmio_writable (.Physaddr (address + 0#64 + 0#64)) width) source = _ at ran
  have zero : ∀ a : BitVec 64, a + 0#64 = a := BitVec.add_zero
  simpa only [zero] using ran

/-- The store's effective-address validation performs no writes, including on faults. -/
theorem readOnly_mem_write_ea (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (mem_write_ea address width .Machine (.Store .Data) .PBMT_PMA false false false) := by
  unfold mem_write_ea
  apply ReadOnlyEAt.runE
  apply ReadOnlyEAt.bindE
  · apply (readOnly_check_pma source cfg address width true).lift.bindE
    intro result
    cases result
    · exact ReadOnlyEAt.pure source _
    · exact ReadOnlyEAt.earlyReturn source _
  · rintro ⟨splittable, granule⟩
    apply (readOnly_split_misaligned source address width granule splittable).lift.bindE
    rintro ⟨count, size⟩
    apply ReadOnlyEAt.bindE_of_run (show (runSail (write_kind_of_flags false false false)) source =
      .ok write_kind.Write_plain source from rfl)
    apply ReadOnlyEAt.bindE
    · apply ReadOnlyEAt.untilE
      · intro value
        exact ReadOnlyEAt.pure source _
      · rintro ⟨finished, index⟩
        apply ReadOnlyEAt.bindE_of_run (show (runSail (PreSail.sail_assert true "loop dummy assert")) source =
          .ok () source from rfl)
        apply ReadOnlyEAt.bindE_of_run (run_pmpCheck_none _ _ _ source cfg.init cfg.toValidMemConfig.h_pmp_off)
        apply ReadOnlyEAt.bindE
        · apply ReadOnlyEAt.bindE_of_run (run_mmio_writable_false source cfg _ _)
          exact (ReadOnlyAt.of_run (run_write_ram_ea _ _ _ source)).lift
        · intro value
          exact ReadOnlyEAt.pure source _
    · intro value
      exact ReadOnlyEAt.pure source _

/-- Computing the virtual page split is read-only, including a failed internal assertion. -/
theorem readOnly_split_on_page_boundary (source : SailState) (address : BitVec 64) (width : ℕ) :
    ReadOnlyAt source (split_on_page_boundary address width) := by
  simp only [split_on_page_boundary]
  split
  · exact ReadOnlyAt.pure source _
  · exact (readOnly_assert source _ _).bind fun _ => ReadOnlyAt.pure source _

/-- Computing a fault address observes PMA regions but leaves the complete state unchanged. -/
theorem run_exception_vaddr_sp1 (source : SailState) (cfg : SailConfigured source)
    (virtual : virtaddr) (physical fault : physaddr) :
    ∃ address, runSail (exception_vaddr sp1AccessInfo virtual physical fault) source = .ok address source := by
  rcases virtual with ⟨virtual⟩
  rcases physical with ⟨physical⟩
  rcases fault with ⟨fault⟩
  simp only [exception_vaddr, sp1AccessInfo, Functions.xlen]
  rw [run_bind_of_run source _ _ (run_is_vmem_active_machine source)]
  simp only [Bool.false_eq_true, ite_false, pure_bind]
  rw [run_readReg_bind_of_isInitialized source Register.pma_regions cfg.init]
  simp only [plat_invalid_physical_address, ite_self]
  exact ⟨_, rfl⟩

/-- Creating a memory trap reports the current privilege and PC without taking the trap. -/
theorem run_memory_exception (source : SailState) (cfg : SailConfigured source)
    (address : BitVec 64) (error : ExceptionType) (info : AccessInfo) :
    (runSail (memory_exception error address info)) source = .ok
      (.Trap (source.regs.get Register.cur_privilege (cfg.init _),
        mem_exception_context error address info,
        source.regs.get Register.PC (cfg.init _))) source := by
  simp only [memory_exception, trap]
  rw [Sail.run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
    Sail.run_readReg_bind_of_isInitialized source Register.PC cfg.init]
  rfl

end SP1Clean.SailMem
