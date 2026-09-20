import Machine.Core.Step

/-! # Labeled machines

A `LabeledMachine` bundles a state type, an event (label) type, the labeled step relation, and
a terminal predicate at which no step is available. It carries no clock, no host, and no field:
those are choices of a particular instance. Its PolyFun view is `LabeledMachine.system`.
-/

namespace Machine

open PFunctor

/-- A transition system with observable labels and a stuck terminal predicate. -/
structure LabeledMachine where
  State : Type
  Event : Type
  Step : State → Event → State → Prop
  Terminal : State → Prop := fun _ => False
  terminal_stuck : ∀ {s : State} {e : Event} {t : State}, Terminal s → ¬ Step s e t := by simp

namespace LabeledMachine

/-- The PolyFun dynamical system whose directions are the proved steps. -/
def system (m : LabeledMachine) : DynSystem m.State (stepInterface m.Step) := stepSystem m.Step

/-- The label carried by each direction. -/
def eventMap (m : LabeledMachine) : m.system.EventMap m.Event := stepEventMap m.Step

/-- A machine whose labeled steps have unique targets. -/
def Deterministic (m : LabeledMachine) : Prop :=
  ∀ {s : m.State} {e : m.Event} {t t' : m.State}, m.Step s e t → m.Step s e t' → t = t'

end LabeledMachine

end Machine
