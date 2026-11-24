import SP1Clean.Proofs.Completeness.MixedAccessFrontier
import SP1Clean.Soundness.Grounding.MemoryCell

/-! # Values at an untouched Memory frontier

The same frontier that supplies the compiler's incoming timestamps also identifies cells
still holding the authenticated source value. The proof uses the official ordinary retirement,
the decoded store width, and the full padded HINT_READ write.
-/

namespace SP1Clean.TraceGen
open Semantics Machine FormalModel.Shard Soundness Soundness.Target LeanRV64D

private theorem aligned_store_cell {base : BitVec 64} {imm : BitVec 12} {width : word_width}
    (valid : storeWidthOK width = true) (aligned : (memoryEffectiveAddress base imm).toNat % width.toNat = 0)
    (offset : ℕ) (bound : offset < width.toNat) :
    ((memoryEffectiveAddress base imm).toNat + offset) / 8 = (memoryRamCell base imm).toNat := by
  have limit := (memoryEffectiveAddress base imm).isLt
  simp only [memoryRamCell, ramCellOfByteAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (memoryEffectiveAddress base imm).toNat / 8 < 2 ^ 61)]
  simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with ((rfl | rfl) | rfl) | rfl <;> norm_num at aligned bound <;> omega

private theorem ordinary_ram_untouched {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {view : SP1TransitionView} {plan : InstructionAccessPlan}
    (step : ExecutionStep policy program source .ordinary target)
    (cfg : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (encoded : ordinaryEncodedAt program source.sail)
    (projected : projectSP1Transition? program ⟨source.sail, ⟨.ordinary, target.sail⟩⟩ = some view)
    (compiled : instructionAccessPlan? view.decoded source.sail target.sail = some plan)
    (cell : RamCell) (fresh : MemLoc.ram cell ∉ plan.map PlannedTouch.loc) :
    locContent target.sail (.ram cell) = locContent source.sail (.ram cell) := by
  obtain ⟨pc, word, instr, atPc, fetched, decode, image, routed, memory⟩ := encoded
  have actual := decodeLocated?_eq_some_of (located := ⟨source.sail, ⟨.ordinary, target.sail⟩⟩) atPc fetched (decode _ cfg)
  have same := Option.some.inj ((projectSP1Transition?_decode projected).symm.trans actual)
  rw [same] at compiled
  let mask := fun address : ℕ => decide (address / 8 = cell.toNat)
  have checked : InstructionWrite.check mask source.sail.get_reg? instr = true := by
    by_cases store : ∃ imm rs2 rs1 width, instr = .STORE (imm, rs2, rs1, width)
    · obtain ⟨imm, rs2, rs1, width, rfl⟩ := store
      obtain ⟨base, observed, _, aligned⟩ := memory
      have valid : storeWidthOK width = true := image
      refine (InstructionWrite.check_store_iff mask _ _ _ _ _ valid).mpr ⟨base, observed, ?_⟩
      intro offset bound
      apply decide_eq_false
      rw [aligned_store_cell valid aligned offset bound]
      intro equal
      exact fresh (BitVec.eq_of_toNat_eq equal ▸ storePlan_cell observed compiled)
    · apply InstructionWrite.check_of_nonstore mask _ instr image routed
      exact fun imm rs2 rs1 width equal => store ⟨imm, rs2, rs1, width, equal⟩
  cases step with
  | ordinary _ _ normal _ =>
    have framed := Advance.ordinary_normal_frame cfg loaded (readOnly := mask) ⟨pc, word, instr, atPc, fetched, decode, checked⟩ normal
    apply locContent_ram_congr_cell
    intro i
    apply framed.2
    apply decide_eq_true
    rw [Soundness.RamCell.baseAddr_toNat]
    have := i.isLt
    omega

/-- An unposted host RAM cell retains its value, including across WRITE and HINT_READ.
The mandatory final padding cell of a HINT_READ always has positive outgoing time. -/
theorem syscall_ram_frontier_zero {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {call : CoreSyscallEvent} (step : ExecutionStep policy program source (.syscall call) target)
    (prior : AccessFrontier) (cell : RamCell) (zero : syscallFrontier prior source.clock call (.ram cell) = 0) :
    prior (.ram cell) = 0 ∧ locContent target.sail (.ram cell) = locContent source.sail (.ram cell) := by
  have old : prior (.ram cell) = 0 := by
    simp only [syscallFrontier, AccessSlot.recordOffset_ram] at zero
    split_ifs at zero
    omega
  refine ⟨old, ?_⟩
  cases step with
  | syscall success =>
    obtain ⟨pc, execution, _, _, ran, _, moved, event⟩ := HostState.step_observations success
    rw [event] at zero
    rw [moved]
    apply locContent_ram_congr_cell
    intro i
    change (execution.effect.applyMemory source.sail.mem).get? _ = _
    cases written : execution.effect.write with
    | none => simp only [HostEffect.applyMemory, written]
    | some write =>
      have kind := (HostState.executeKind_write_origin ((source.host.run_eq_some_iff ..).mp ran).2.2.2.2.2 write written).1
      obtain ⟨actual, actualWrite, frontier⟩ := syscallFrontier_hintRead ran kind prior source.clock pc
      cases Option.some.inj (written.symm.trans actualWrite)
      rw [frontier] at zero
      have outside : cell.toNat ∉ (MemorySpan.mk write.address write.bytes.length).cells := by
        intro member
        rw [ite_eq_left member] at zero
        omega
      simp only [HostEffect.applyMemory, written]
      apply write.read_outside
      simpa only [Soundness.RamCell.baseAddr_toNat] using (MemorySpan.mk write.address write.bytes.length).byte_outside cell.toNat i i.isLt outside

private theorem value_at_zero_frontier {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) (loc : MemLoc)
    (ordinary : ∀ {current next : ExecutionState} {view : SP1TransitionView} {plan : InstructionAccessPlan},
      ExecutionStep (policy p image) image.program current .ordinary next →
      SailConfigured current.sail → RomLoaded image.program current.sail → ordinaryEncodedAt image.program current.sail →
      projectSP1Transition? image.program ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view →
      instructionAccessPlan? view.decoded current.sail next.sail = some plan → loc ∉ plan.map PlannedTouch.loc →
        locContent next.sail loc = locContent current.sail loc)
    (host : ∀ {current next : ExecutionState} {call : CoreSyscallEvent}, ExecutionStep (policy p image) image.program current (.syscall call) next →
      ∀ prior : AccessFrontier, syscallFrontier prior current.clock call loc = 0 →
        prior loc = 0 ∧ locContent next.sail loc = locContent current.sail loc)
    {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (built : mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier))
    (zero : frontier loc = 0) : locContent current.sail loc = locContent source.realize.sail loc := by
  induction cut generalizing current frontier with
  | zero => cases built; rfl
  | succ cut ih =>
    cases present : events[cut]? with
    | none =>
      have ended := List.getElem?_eq_none_iff.mp present
      apply ih (frontier := frontier) _ zero
      simpa only [mixedAccessPrefix, List.take_of_length_le ended, List.take_of_length_le (Nat.le_succ_of_le ended)] using built
    | some event =>
      obtain ⟨before, prior, atCut, beforeBuilt, _⟩ := admissibleExecution_mixedAccessPrefix execution cut
      rw [mixedAccessPrefix_succ _ _ _ _ present, beforeBuilt, Option.bind_some] at built
      cases event with
      | ordinary =>
        obtain ⟨before', next, view, row, atCut', step, projected, made, _⟩ := admissibleExecution_compile_at execution present prior
        cases Option.some.inj (atCut'.symm.trans atCut)
        have generated : mixedAccessStep (policy p image) image.program (before, prior) .ordinary = some (next, row.nextFrontier) := by
          simp [mixedAccessStep, emitMixedAccessStep?, step.replay, projected, made]
        cases Option.some.inj (generated.symm.trans built)
        rw [compileInstructionEvent?_nextFrontier made, advancePlan_zero_iff] at zero
        have frame := execution.1.frame_prefix atCut
        exact (ordinary step frame.1 frame.2.1 ((execution.2.1 _ _ _ present atCut).2 rfl)
          projected (compileInstructionEvent?_accessPlan_generated projected made) zero.2).trans (ih beforeBuilt zero.1)
      | syscall call =>
        obtain ⟨before', next, atCut', step⟩ := execution.1.2.step_at present
        cases Option.some.inj (atCut'.symm.trans atCut)
        have generated : mixedAccessStep (policy p image) image.program (before, prior) (.syscall call) =
            some (next, syscallFrontier prior before.clock call) := by simp [mixedAccessStep, emitMixedAccessStep?, step.replay]
        cases Option.some.inj (generated.symm.trans built)
        have kept := host step prior zero
        exact kept.2.trans (ih beforeBuilt kept.1)

private theorem ordinary_register_untouched {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {view : SP1TransitionView} {plan : InstructionAccessPlan}
    (step : ExecutionStep policy program source .ordinary target)
    (cfg : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (projected : projectSP1Transition? program ⟨source.sail, ⟨.ordinary, target.sail⟩⟩ = some view)
    (compiled : instructionAccessPlan? view.decoded source.sail target.sail = some plan)
    (index : BitVec 5) (fresh : MemLoc.reg index ∉ plan.map PlannedTouch.loc) :
    locContent target.sail (.reg index) = locContent source.sail (.reg index) := by
  cases step with
  | @ordinary next _ _ normal permitted =>
    obtain ⟨pc, word, instr, atPc, fetched, decode, checked⟩ := permitted
    have actual := decodeLocated?_eq_some_of (located := ⟨source.sail, ⟨.ordinary, next⟩⟩) atPc fetched (decode source.sail cfg)
    have same := Option.some.inj ((projectSP1Transition?_decode projected).symm.trans actual)
    rw [same] at compiled
    exact (Advance.permitted_normal_frame cfg loaded atPc fetched decode checked normal).2.2.2 index
      (fun selected => fresh (instructionAccessPlan_destination selected compiled))

private theorem syscall_register_frontier_zero {policy : HostPolicy} {program : GuestProgram} {source target : ExecutionState}
    {call : CoreSyscallEvent} (step : ExecutionStep policy program source (.syscall call) target)
    (prior : AccessFrontier) (index : BitVec 5) (zero : syscallFrontier prior source.clock call (.reg index) = 0) :
    prior (.reg index) = 0 ∧ locContent target.sail (.reg index) = locContent source.sail (.reg index) := by
  change advancePlan prior source.clock (syscallRegisterPlan call) (.reg index) = 0 at zero
  rw [advancePlan_zero_iff] at zero
  refine ⟨zero.1, step.syscall_sail_frame.2.1 index ?_⟩
  rintro rfl
  exact zero.2 (by simp [syscallRegisterPlan])

/-- At every cut of a complete mixed execution, every register and RAM cell still at its genesis time holds its incoming Sail value. -/
theorem admissibleExecution_untouched {limits : ResourceLimits} {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits p image source target events) {cut : ℕ} {current : ExecutionState} {frontier : AccessFrontier}
    (built : mixedAccessPrefix (policy p image) image.program source.realize events cut = some (current, frontier))
    (loc : MemLoc) (zero : frontier loc = 0) :
    locContent current.sail loc = locContent source.realize.sail loc := by
  cases loc with
  | ram cell =>
    exact value_at_zero_frontier execution (.ram cell)
      (fun step cfg loaded encoded projected compiled => ordinary_ram_untouched step cfg loaded encoded projected compiled cell)
      (fun step prior => syscall_ram_frontier_zero step prior cell) built zero
  | reg index =>
    exact value_at_zero_frontier execution (.reg index)
      (fun step cfg loaded _ projected compiled => ordinary_register_untouched step cfg loaded projected compiled index)
      (fun step prior => syscall_register_frontier_zero step prior index) built zero

end SP1Clean.TraceGen
