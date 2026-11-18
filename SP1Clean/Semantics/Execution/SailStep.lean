module

public import SP1Clean.Semantics.Execution.GuestBoot

/-! # One official Sail step

The official Sail `try_step` function is the instruction semantics. `stepOnce` totalizes one step
with `Option`: an interpreter error is `none`, never a successful halt. The complete execution step
and its replay (`Semantics/Execution/ExecutionReplay`) use it for ordinary instructions. -/

@[expose] public section

open LeanRV64D

namespace SP1Clean.Machine

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target

/-- SP1 starts execution with a zeroed integer register file. -/
def RegistersZero (state : SailState) : Prop :=
  ∀ index : BitVec 5, state.get_reg? index = some 0

/-- One deterministic Sail step, totalized with `Option`. -/
noncomputable def stepOnce (state : SailState) : Option SailState :=
  match (runSail (try_step 0 false)) state with
  | .ok _ next => some next
  | .error _ _ => none

end SP1Clean.Machine
