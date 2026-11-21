module

public import SP1Clean.Semantics.Execution.ExecutionReplay
public import SP1Clean.Semantics.ISA.JumpLink

/-! # Released jump-link encoding on complete local execution paths

Each ordinary cut reads its actual source PC, committed instruction word and official Sail decode.
Only the two jump opcodes write a link. The execution relation separately supplies the authenticated
fetch and successful decode at every ordinary cut.
-/

@[expose] public section

namespace SP1Clean.Semantics

open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D LeanRV64D.Functions

/-- Use the same three-limb link check as the instruction-event predicates. -/
def instructionLinkFits (pc : BitVec 64) : instruction → Prop
  | .JAL (_, .Regidx rd) | .JALR (_, _, .Regidx rd) => JumpLinkFits pc.toNat (rd ≠ 0)
  | _ => True

/-- The encoding condition for the authenticated source of an ordinary step. -/
def ReleaseLinkAt (program : GuestProgram) (state : SailState) : Prop :=
  ∀ pc word decoded, state.regs.get? Register.PC = some pc → program.fetchWord pc = some word →
    runSail (ext_decode word) state = .ok decoded state → instructionLinkFits pc decoded

/-- The actual fetch and decode completely determine the release check. -/
theorem releaseLinkAt_iff {program : GuestProgram} {state : SailState} {pc : BitVec 64}
    {word : BitVec 32} {decoded : instruction} (atPc : state.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (ran : runSail (ext_decode word) state = .ok decoded state) :
    ReleaseLinkAt program state ↔ instructionLinkFits pc decoded := by
  constructor
  · exact fun all => all pc word decoded atPc fetched ran
  · intro fits pc' word' decoded' observed fetched' ran'
    obtain rfl := Option.some.inj (observed.symm.trans atPc)
    obtain rfl := Option.some.inj (fetched'.symm.trans fetched)
    cases ran'.symm.trans ran
    exact fits

namespace ExecutionPath

/-- Check precisely the actual ordinary source states reached by replay of this tape. -/
def ReleaseLinks (policy : HostPolicy) (program : GuestProgram)
    (source : ExecutionState) (events : List ExecutionEvent) : Prop :=
  ∀ cut current, events[cut]? = some .ordinary →
    replayEvents? policy program source (events.take cut) = some current → ReleaseLinkAt program current.sail

variable {policy : HostPolicy} {program : GuestProgram} {source middle : ExecutionState}
  {event : ExecutionEvent} {events first second : List ExecutionEvent}

/-- Empty segments and segments containing only host calls have no link writes. -/
theorem releaseLinks_of_no_ordinary (none : .ordinary ∉ events) : ReleaseLinks policy program source events := by
  intro cut _ ordinary
  exact (none (List.mem_of_getElem? ordinary)).elim

@[simp] theorem releaseLinks_nil : ReleaseLinks policy program source [] := releaseLinks_of_no_ordinary (by simp)

/-- A one-instruction tape checks the supplied source, without demanding a terminal fetch. -/
theorem releaseLinks_singleton : ReleaseLinks policy program source [.ordinary] ↔ ReleaseLinkAt program source.sail := by
  constructor
  · exact fun all => all 0 source rfl rfl
  · intro holds n current atCut replay
    cases n with
    | zero => cases Option.some.inj replay; exact holds
    | succ n => simp at atCut

/-- Peeling a real step tests its own source on an ordinary retirement. -/
theorem releaseLinks_cons_iff (step : ExecutionStep policy program source event middle) :
    ReleaseLinks policy program source (event :: events) ↔
      (event = .ordinary → ReleaseLinkAt program source.sail) ∧ ReleaseLinks policy program middle events := by
  constructor
  · intro all
    refine ⟨fun ordinary => all 0 source (by simp only [ordinary, List.getElem?_cons_zero]) rfl, ?_⟩
    intro n current ordinary replay
    apply all (n + 1) current (by simpa only [List.getElem?_cons_succ] using ordinary)
    simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay
  · rintro ⟨head, tail⟩ n current ordinary replay
    cases n with
    | zero =>
      cases Option.some.inj replay
      exact head (Option.some.inj ordinary)
    | succ n =>
      apply tail n current (by simpa only [List.getElem?_cons_succ] using ordinary)
      simpa only [List.take_succ_cons, replayEvents?, step.replay, Option.bind_some] using replay

/-- A shard boundary carries the exact source for the remaining tape. -/
theorem releaseLinks_append_iff (path : ExecutionPath policy program source first middle) :
    ReleaseLinks policy program source (first ++ second) ↔
      ReleaseLinks policy program source first ∧ ReleaseLinks policy program middle second := by
  induction path with
  | nil => simp only [List.nil_append, releaseLinks_nil, true_and]
  | cons step _ ih => simp only [List.cons_append, releaseLinks_cons_iff step, ih, and_assoc]

end ExecutionPath
end SP1Clean.Semantics
