import Machine.Core.Machine

/-! # Finite labeled paths and their PolyFun view

`Path m s es t` is the proof-free semantic spine: a finite run of the labeled machine `m` from
`s` to `t` carrying exactly the labels `es`. It composes and splits at any step, is stuck at a
terminal state, and is deterministic when the machine is. PolyFun's finite `Prefix` of
`m.system` is an equivalent certified view (`exists_prefix`, `path_of_prefix`); counted reachability
`Segment` is exactly `ReachableIn` (`Segment.iff_reachableIn`). The view introduces no padding
step and asserts nothing about any circuit.
-/

namespace Machine

open PFunctor

/-- A finite run carrying exactly its labels. -/
inductive Path (m : LabeledMachine) : m.State → List m.Event → m.State → Prop
  | nil (s : m.State) : Path m s [] s
  | cons {s mid t : m.State} {e : m.Event} {es : List m.Event} :
      m.Step s e mid → Path m mid es t → Path m s (e :: es) t

namespace Path

variable {m : LabeledMachine}

theorem nil_iff {s t : m.State} : Path m s [] t ↔ t = s := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil _

theorem cons_iff {s t : m.State} {e : m.Event} {es : List m.Event} :
    Path m s (e :: es) t ↔ ∃ mid, m.Step s e mid ∧ Path m mid es t := by
  constructor
  · intro h
    cases h with
    | cons step rest => exact ⟨_, step, rest⟩
  · rintro ⟨mid, step, rest⟩
    exact .cons step rest

/-- Paths compose at their shared endpoint. -/
theorem append {s mid t : m.State} {first second : List m.Event} :
    Path m s first mid → Path m mid second t → Path m s (first ++ second) t
  | .nil _, right => right
  | .cons step rest, right => .cons step (append rest right)

theorem append_iff {s t : m.State} {first second : List m.Event} :
    Path m s (first ++ second) t ↔ ∃ mid, Path m s first mid ∧ Path m mid second t := by
  constructor
  · intro h
    induction first generalizing s with
    | nil => exact ⟨s, .nil s, h⟩
    | cons e es ih =>
        obtain ⟨mid₁, step, rest⟩ := cons_iff.mp h
        obtain ⟨mid, left, right⟩ := ih rest
        exact ⟨mid, .cons step left, right⟩
  · rintro ⟨mid, left, right⟩
    exact left.append right

/-- A path can be cut after any number of steps. -/
theorem split (cut : ℕ) {s t : m.State} {es : List m.Event} (path : Path m s es t) :
    ∃ mid, Path m s (es.take cut) mid ∧ Path m mid (es.drop cut) t := by
  rw [← List.take_append_drop cut es] at path
  exact append_iff.mp path

/-- Nothing moves from a terminal state. -/
theorem of_terminal {s t : m.State} {es : List m.Event} (terminal : m.Terminal s)
    (path : Path m s es t) : es = [] ∧ t = s := by
  cases path with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons step _ => exact absurd step (m.terminal_stuck terminal)

/-- Equal labels from equal sources reach equal targets in a deterministic machine. -/
theorem deterministic (det : m.Deterministic) :
    ∀ {s t t' : m.State} {es : List m.Event}, Path m s es t → Path m s es t' → t = t'
  | _, _, _, _, .nil _, .nil _ => rfl
  | _, _, _, _, .cons step rest, .cons step' rest' => by
      obtain rfl := det step step'
      exact deterministic det rest rest'

/-- Every path is a PolyFun orbit of the machine's system with the same labels and endpoint. -/
theorem exists_prefix {s t : m.State} {es : List m.Event} (path : Path m s es t) :
    ∃ orbit : DynSystem.Prefix m.system s es.length,
      orbit.last = t ∧ orbit.events m.eventMap = es := by
  induction path with
  | nil _ => exact ⟨.nil, rfl, rfl⟩
  | cons step _ ih =>
      obtain ⟨orbit, endpoint, labels⟩ := ih
      exact ⟨.step ⟨_, _, ⟨step⟩⟩ orbit, endpoint, congrArg (_ :: ·) labels⟩

end Path

/-- An orbit of the system is a path: the view adds no idle or padding step. -/
theorem path_of_prefix {m : LabeledMachine} {s : m.State} {n : ℕ}
    (orbit : DynSystem.Prefix m.system s n) : Path m s (orbit.events m.eventMap) orbit.last := by
  induction orbit with
  | nil => exact .nil _
  | step d _ ih => exact .cons d.2.2.down ih

theorem prefix_events_length {m : LabeledMachine} {s : m.State} {n : ℕ}
    (orbit : DynSystem.Prefix m.system s n) : (orbit.events m.eventMap).length = n := by
  induction orbit with
  | nil => rfl
  | step _ _ ih => exact congrArg Nat.succ ih

/-- Counted reachability along labeled paths. -/
def Segment (m : LabeledMachine) (s : m.State) (n : ℕ) (t : m.State) : Prop :=
  ∃ es : List m.Event, es.length = n ∧ Path m s es t

/-- Counted paths are exactly PolyFun's finite reachability. -/
theorem Segment.iff_reachableIn {m : LabeledMachine} {s t : m.State} {n : ℕ} :
    Segment m s n t ↔ m.system.ReachableIn n s t := by
  constructor
  · rintro ⟨es, rfl, path⟩
    obtain ⟨orbit, endpoint, _⟩ := path.exists_prefix
    exact ⟨orbit, endpoint⟩
  · rintro ⟨orbit, rfl⟩
    exact ⟨_, prefix_events_length orbit, path_of_prefix orbit⟩

end Machine
