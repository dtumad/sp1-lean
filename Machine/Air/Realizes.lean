import Machine.Core.Path
import ToClean.Air.CompleteEnsemble

/-! # A flat AIR ensemble realizing a labeled machine

`Realizes m ens boundary admissible` says that raw acceptance of the Clean ensemble `ens` at a
public input is exactly the existence of an admissible labeled path of `m` between the boundary
states read from that public input: soundness in Clean's own `Ensemble.Soundness` shape and a
proof-independent compiler in the `EnsembleCompiler` shape. Neither direction may mention rows,
provers, or compiler success in its domain; `admissible` is the semantic resource profile. The
single statement is `Realizes.statement_iff`; reachability of the boundary is its corollary.
-/

namespace Machine

open Air.Flat PFunctor

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The semantic reading of a public input: a path between its boundary states, admissible. -/
def Interpretation (m : LabeledMachine) (boundary : PublicIO F → m.State × m.State)
    (admissible : PublicIO F → List m.Event → Prop) (publicInput : PublicIO F)
    (events : List m.Event) : Prop :=
  Path m (boundary publicInput).1 events (boundary publicInput).2 ∧ admissible publicInput events

/-- An ensemble realizes a machine: sound and complete for admissible paths at every boundary. -/
structure Realizes (m : LabeledMachine) (ens : Ensemble F PublicIO)
    (boundary : PublicIO F → m.State × m.State)
    (admissible : PublicIO F → List m.Event → Prop) where
  sound : ens.Soundness (fun _ => True)
    (fun publicInput => ∃ events, Interpretation m boundary admissible publicInput events)
  compiler : EnsembleCompiler ens (List m.Event) (Interpretation m boundary admissible)

namespace Realizes

variable {m : LabeledMachine} {ens : Ensemble F PublicIO}
  {boundary : PublicIO F → m.State × m.State} {admissible : PublicIO F → List m.Event → Prop}

/-- The single statement: raw acceptance is exactly an admissible path between the boundary states. -/
theorem statement_iff (r : Realizes m ens boundary admissible) (publicInput : PublicIO F) :
    ens.Statement publicInput ↔
      ∃ events, Path m (boundary publicInput).1 events (boundary publicInput).2 ∧
        admissible publicInput events :=
  (r.compiler.toCompleteEnsemble r.sound).statement_iff publicInput trivial

/-- An accepted public input has a reachable boundary. -/
theorem reachable_of_statement (r : Realizes m ens boundary admissible) {publicInput : PublicIO F}
    (accepted : ens.Statement publicInput) :
    ∃ n, m.system.ReachableIn n (boundary publicInput).1 (boundary publicInput).2 := by
  obtain ⟨events, path, _⟩ := (r.statement_iff publicInput).mp accepted
  exact ⟨events.length, Segment.iff_reachableIn.mp ⟨events, rfl, path⟩⟩

end Realizes

end Machine
