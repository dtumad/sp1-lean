module

public import SP1Clean.Semantics.Sail.SailPlatform
public import SP1Clean.Semantics.Sail.ExecutionFootprint

/-! # Sail retirement registers across the execute stage

Official instruction retirement refreshes interrupts before execution, records its counter
decision, and clears the event marker after ticking PC. These register projections describe
the incoming and outgoing states of that one interpreter transition.
-/

@[expose] public section

namespace SP1Clean.Semantics
open LeanRV64D LeanRV64D.Functions SP1Clean.TryStepReduction

/-- The official machine-mode retirement decision, with a total fallback on absent registers.
Successful interpreter evaluation checks the filter when retirement is enabled and proves agreement. -/
def retirementEnabled (state : SailState) : Bool :=
  (_get_Counterin_IR ((state.regs.get? Register.mcountinhibit).getD 0) == 0#1) &&
    (counter_priv_filter_bit ((state.regs.get? Register.minstretcfg).getD 0) Privilege.Machine == 0#1)

/-- The data-only decision agrees with the actual successful Sail filter computation. -/
theorem retirementEnabled_of_run {state : SailState} {enabled : Bool}
    (success : (runSail (should_inc_minstret Privilege.Machine)) state = .ok enabled state) :
    retirementEnabled state = enabled := by
  simp only [should_inc_minstret, andM, toBool, runSail_bind, Sail.run_readReg] at success
  cases inhibit : state.regs.get? Register.mcountinhibit with
  | none => simp only [inhibit] at success; cases success
  | some inhibitValue =>
    simp only [inhibit] at success
    cases active : (_get_Counterin_IR inhibitValue == 0#1) with
    | false =>
      simp only [active, runSail_pure] at success
      cases success
      simp only [retirementEnabled, inhibit, Option.getD_some, active, Bool.false_and]
    | true =>
      simp only [active, runSail_pure, runSail_bind, Sail.run_readReg] at success
      cases filter : state.regs.get? Register.minstretcfg with
      | none => simp only [filter] at success; cases success
      | some filterValue =>
        simp only [filter] at success
        cases success
        simp only [retirementEnabled, inhibit, filter, Option.getD_some, active, Bool.true_and]

/-- Register entries that the supported RISC-V execute stage leaves in place. -/
def PreservesRetirementRegisters (source target : SailState) : Prop :=
  ∀ reg, reg ∈ [Register.mcountinhibit, .minstretcfg, .minstret_increment, .minstret, .misa, .hvip, .mip] →
    target.regs.get? reg = source.regs.get? reg

/-- The instruction's write footprint frames all seven retirement-control reads. -/
theorem ExecuteFrame.retirementRegisters {source target : SailState} (frame : ExecuteFrame source target) :
    PreservesRetirementRegisters source target := by
  intro reg member
  apply frame.registers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, fun index _ => by unfold reg_idx_to_Register; split <;> decide⟩

/-- The official update_mip and minstret prelude followed by the staged sequential nextPC. -/
def retirementPrelude (source : SailState) (increment : Bool) (nextPC : BitVec 64) : SailState :=
  { source with regs := ((source.regs.insert .mip (refreshedMip source)).insert .minstret_increment increment).insert .nextPC nextPC }

/-- The complete dynamic bookkeeping effects of one normally retiring instruction. -/
structure OrdinaryBookkeeping (source target : SailState) : Prop where
  enabled : retirementEnabled target = retirementEnabled source
  flag : target.regs.get? Register.minstret_increment = some (retirementEnabled source)
  counter : target.regs.get? Register.minstret = (source.regs.get? Register.minstret).map
    (fun value => value + if retirementEnabled source then 1 else 0)
  refresh : refreshedMip target = refreshedMip source
  interrupts : target.regs.get? Register.mip = some (refreshedMip source)
  eventIndex : target.regs.get? Register.written_event_index = some none

/-- The real retirement tail transports the seven framed execute-stage entries. Its counter
uses the value actually read by Sail and wraps at word width. -/
theorem OrdinaryBookkeeping.of_tail {source post actual : SailState} {increment : Bool} {nextPC : BitVec 64}
    (decision : retirementEnabled source = increment)
    (held : PreservesRetirementRegisters (retirementPrelude source increment nextPC) post)
    (initialized : post.isInitialized)
    (frame : ∀ r : Register, r ≠ .PC → r ≠ .minstret → r ≠ .written_event_index →
      actual.regs.get? r = post.regs.get? r)
    (counter : actual.regs.get? Register.minstret = (post.regs.get? Register.minstret).map (fun value =>
      if (true && post.regs.get Register.minstret_increment (initialized _)) = true then Sail.BitVec.addInt value 1 else value))
    (cleared : actual.regs.get? Register.written_event_index = some none) : OrdinaryBookkeeping source actual := by
  let staged := retirementPrelude source increment nextPC
  have same (r : Register) (included : r ∈ [Register.mcountinhibit, .minstretcfg, .minstret_increment, .misa, .hvip, .mip]) :
      actual.regs.get? r = staged.regs.get? r := by
    have keep : r ∈ [Register.mcountinhibit, .minstretcfg, .minstret_increment, .minstret, .misa, .hvip, .mip] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at included ⊢
      tauto
    apply (frame r ?_ ?_ ?_).trans (held r keep) <;> intro h <;> subst r <;> simp at included
  have inhibit := same .mcountinhibit (by simp)
  have filter := same .minstretcfg (by simp)
  have isa := same .misa (by simp)
  have injected := same .hvip (by simp)
  have mip := same .mip (by simp)
  have flag := same .minstret_increment (by simp)
  have postFlag := held .minstret_increment (by simp)
  have postCounter := held .minstret (by simp)
  simp only [staged, retirementPrelude, Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq,
    ↓reduceDIte] at inhibit filter isa injected mip flag postFlag postCounter
  have actualFlag : post.regs.get Register.minstret_increment (initialized _) = increment :=
    Option.some.inj ((Std.ExtDHashMap.get?_eq_some_get (initialized Register.minstret_increment)).symm.trans postFlag)
  refine ⟨?_, ?_, ?_, ?_, mip, cleared⟩
  · simp only [retirementEnabled, inhibit, filter]
  · rw [decision]
    exact flag
  · rw [counter, actualFlag, postCounter, decision]
    cases increment <;> simp [Sail.BitVec.addInt]
  · unfold refreshedMip
    rw [isa, injected, mip, Option.getD_some]
    exact refreshedMipBits_idempotent _ _ _

end SP1Clean.Semantics
