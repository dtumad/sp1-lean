import PolyFun.PFunctor.Dynamical.Run

/-! # Labeled step relations as PolyFun interfaces

## Gap against upstream

PolyFun presents a transition system as a `DynSystem`: positions are exposed states and
directions are the moves available there. `PolyFun.Interaction.Concurrent.Machine` builds that
view from an enabled-event type over `PFunctor.univ`. This file builds it from a **labeled step
relation** `Step : S → E → S → Prop` instead: a direction at `s` is a label, a target, and a proof
that the labeled step is valid, so an orbit of the system is exactly a valid labeled execution and
no idle or padding step is representable. The same construction was written twice in the SP1
development (`eventInterface`, `executionInterface`); this is the one copy.
-/

namespace Machine

open PFunctor

/-- The dependent interface of a labeled step relation: positions are states, and the directions
at a state are its proved next steps. -/
def stepInterface {S E : Type} (Step : S → E → S → Prop) : PFunctor where
  A := S
  B := fun s => Σ e : E, Σ t : S, PLift (Step s e t)

/-- The dynamical system that follows the chosen step. -/
def stepSystem {S E : Type} (Step : S → E → S → Prop) : DynSystem S (stepInterface Step) :=
  DynSystem.mk' id fun _ d => d.2.1

/-- The label of a direction. -/
def stepEventMap {S E : Type} (Step : S → E → S → Prop) : (stepSystem Step).EventMap E :=
  fun _ d => d.1

@[simp] theorem stepSystem_expose {S E : Type} (Step : S → E → S → Prop) (s : S) :
    (stepSystem Step).expose s = s := rfl

@[simp] theorem stepSystem_update {S E : Type} (Step : S → E → S → Prop) (s : S)
    (d : (stepInterface Step).B s) : (stepSystem Step).update s d = d.2.1 := rfl

@[simp] theorem stepEventMap_apply {S E : Type} (Step : S → E → S → Prop) (s : S)
    (d : (stepInterface Step).B s) : stepEventMap Step s d = d.1 := rfl

end Machine
