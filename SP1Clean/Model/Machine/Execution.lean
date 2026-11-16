import SP1Clean.Model.Machine.Schedule
import SP1Clean.Model.Machine.Boot
import PolyFun.PFunctor.Dynamical.Basic
import PolyFun.PFunctor.Dynamical.Run

/-! # The Lean-native SP1 execution machine

The official Sail `try_step` function remains the instruction semantics.  This file packages its
deterministic trajectory as a small PolyFun dynamical system: the exposed observation is the current
`Option SailState`, and the sole direction is `PUnit`.  Failure is represented by `none`, which then
stutters, making the transition total without treating an interpreter error as a successful halt.

PolyFun is used only for this semantic transition/run interface.  Circuit construction and Clean's
interaction machinery remain independent of it. -/

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
