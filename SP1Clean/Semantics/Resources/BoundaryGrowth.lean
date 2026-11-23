module

public import SP1Clean.Semantics.Resources.HostReceiptResources
public import SP1Clean.Semantics.Execution.ExecutionFrame

/-! # Growth of the complete boundary payload along an installed execution

An ordinary store touches at most eight byte addresses. A host write may touch many more,
but the installed handlers pay for every emitted byte by consuming incoming host payload.
The Sail output stays fixed throughout the same path.
-/

@[expose] public section

namespace SP1Clean.Semantics

open Machine Soundness.Target

private theorem support_growth {source target : ExecutionState} (base size : ℕ)
    (outside : ∀ address, address < base ∨ base + size ≤ address →
      target.sail.mem.get? address = source.sail.mem.get? address) :
    target.memorySupport.card ≤ source.memorySupport.card + size := by
  classical
  have covered : target.memorySupport ⊆ source.memorySupport ∪ Finset.Ico base (base + size) := by
    intro address live
    by_cases inside : address ∈ Finset.Ico base (base + size)
    · exact Finset.mem_union_right _ inside
    · apply Finset.mem_union_left
      simp only [Finset.mem_Ico] at inside
      have same := outside address (by omega)
      simpa only [ExecutionState.memorySupport, Finset.mem_filter, same] using live
  have both := (Finset.card_le_card covered).trans (Finset.card_union_le ..)
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using both

private theorem ordinary_support_growth {source target : ExecutionState} {program : GuestProgram}
    {readOnly : ℕ → Bool} (configured : SailConfigured source.sail)
    (loaded : RomLoaded program source.sail) (normal : SailRetiresNormally source.sail target.sail)
    (permission : InstructionWrite.PermittedAt readOnly program source.sail) :
    target.memorySupport.card ≤ source.memorySupport.card + 8 := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, checked⟩ := permission
  obtain ⟨supported, routed⟩ := InstructionWrite.check_supported _ _ _ checked
  by_cases store : ∃ offset rs2 rs1 width, decoded = .STORE (offset, rs2, rs1, width)
  · obtain ⟨offset, rs2, rs1, width, rfl⟩ := store
    obtain ⟨base, observed, _⟩ := (InstructionWrite.check_store_iff _ _ _ _ _ _ supported).mp checked
    let start := (memoryEffectiveAddress base offset).toNat
    let mask (address : ℕ) := decide (address < start ∨ start + width.toNat ≤ address)
    have permitted : InstructionWrite.PermittedAt mask program source.sail := by
      refine ⟨pc, word, _, atPc, fetched, decode, (InstructionWrite.check_store_iff _ _ _ _ _ _ supported).mpr
        ⟨base, observed, ?_⟩⟩
      intro index bound
      change decide (start + index < start ∨ start + width.toNat ≤ start + index) = false
      exact decide_eq_false (by omega)
    have growth := support_growth (source := source) (target := target) start width.toNat
      (fun address beyond => (Advance.ordinary_normal_frame configured loaded permitted normal).2 address
        (decide_eq_true beyond))
    change storeWidthOK width = true at supported
    simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at supported
    rcases supported with ((rfl | rfl) | rfl) | rfl <;> exact growth.trans (by omega)
  · have permitted : InstructionWrite.PermittedAt (fun _ => true) program source.sail :=
      ⟨pc, word, decoded, atPc, fetched, decode, InstructionWrite.check_of_nonstore _ _ _ supported routed
        (fun _ _ _ _ same => store ⟨_, _, _, _, same⟩)⟩
    have growth := support_growth (source := source) (target := target) 0 0
      (fun address _ => (Advance.ordinary_normal_frame configured loaded permitted normal).2 address rfl)
    omega

private theorem host_support_growth {source target : ExecutionState} {pc : BitVec 64} {execution : HostExecution}
    (applied : target.sail = execution.apply source.sail pc) :
    target.memorySupport.card ≤ source.memorySupport.card + execution.writeByteCount := by
  cases emitted : execution.effect.write with
  | none =>
    have growth := support_growth (source := source) (target := target) 0 0 (fun address _ => by
      rw [applied]
      simp only [HostExecution.apply, HostEffect.applyMemory, emitted])
    omega
  | some write =>
    rw [HostExecution.writeByteCount_eq emitted]
    apply support_growth write.address
    intro address beyond
    rw [applied]
    simpa only [HostExecution.apply, HostEffect.applyMemory, emitted] using write.read_outside source.sail.mem address beyond

/-- A real installed retirement increases the combined RAM, host and Sail output payload by
at most eight bytes for an ordinary instruction and zero for a host call. -/
theorem ExecutionStep.boundaryPayload_growth {includeVerify : Bool} {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent} (step : ExecutionStep policy program source event target)
    (allowed : HostReceiptProfile.event includeVerify event)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail) :
    target.boundaryPayload ≤ source.boundaryPayload + (if event.isOrdinary then 8 else 0) := by
  have output := (step.sailFrame configured loaded).output
  have paid := HostReceiptProfile.writes_add_hostPayload_le (.cons step (.nil _))
    (fun e member => (List.mem_singleton.mp member) ▸ allowed)
  rw [executionResources_cons step, executionResources_nil] at paid
  simp only [ResourceUsage.combine, ResourceKind.cumulative, ↓reduceIte, ExecutionState.resources,
    ResourceUsage.zero, Nat.zero_add, Nat.add_zero] at paid
  unfold ExecutionState.boundaryPayload
  rw [output]
  cases step with
  | @ordinary target _ _ normal permission =>
    have growth := ordinary_support_growth (target := ⟨target, source.host, source.clock + ordinarySchedule.duration⟩) configured loaded normal permission
    simp only [ExecutionEvent.isOrdinary_ordinary, ↓reduceIte]
    omega
  | @syscall host target event success =>
    obtain ⟨pc, execution, _, _, ran, _, applied, _⟩ := HostState.step_observations success
    have growth := host_support_growth (source := source) (target := ⟨target, host, source.clock + syscallSchedule.duration⟩) applied
    simp only [ExecutionState.eventResources, HostState.eventResources, ran, HostState.executionResources] at paid
    simp only [ExecutionEvent.isOrdinary_syscall, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega

/-- Every arbitrary-length installed segment pays for its peak and its outgoing boundary with
its incoming payload and at most eight bytes per actual ordinary retirement. -/
theorem ExecutionPath.boundaryPayload_growth {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy (image.toGuestProgram valid) source events target) {includeVerify : Bool}
    (allowed : ∀ e ∈ events, HostReceiptProfile.event includeVerify e)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail) :
    let ceiling := source.boundaryPayload + 8 * events.countP ExecutionEvent.isOrdinary
    target.boundaryPayload ≤ ceiling ∧
      executionResources policy (image.toGuestProgram valid) source events .boundaryBytes ≤ ceiling := by
  induction path with
  | nil => simp [ResourceUsage.zero]
  | @cons source middle target event events step _ ih =>
    have next := step.frame configured loaded
    have rom := image.romLoaded_of_readOnly valid
      (fun address selected => next.2 address (protectsRom address selected)) loaded
    obtain ⟨endpoint, suffix⟩ := ih (fun e mem => allowed e (List.mem_cons_of_mem _ mem)) next.1 rom
    have here := step.boundaryPayload_growth (allowed event (List.mem_cons_self ..)) configured loaded
    have noCharge : source.eventResources policy event .boundaryBytes = 0 := by
      cases event <;> simp only [ExecutionState.eventResources, HostState.eventResources]
      split <;> rfl
    rw [executionResources_cons step]
    simp only [List.countP_cons, ResourceUsage.combine, ResourceKind.cumulative, Bool.false_eq_true, ↓reduceIte,
      ExecutionState.resources, noCharge, Nat.max_zero, max_le_iff]
    cases yes : event.isOrdinary <;> simp only [yes, Bool.false_eq_true, ↓reduceIte] at here ⊢ <;> omega

end SP1Clean.Semantics
