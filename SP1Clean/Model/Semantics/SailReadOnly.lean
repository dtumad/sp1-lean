import SP1Clean.Model.Semantics.SailExecuteFrame

/-! # State frames for Sail reads and early returns

These partial-correctness lemmas concern the actual Sail state monad. They include early returns
from `SailME` and bounded loops; an unsuccessful underlying Sail action cannot yield a successful
composite action. No totality or memory-presence premise is needed.
-/

namespace SP1Clean.SailFrame
open Sail Sail.ArchSem LeanRV64D LeanRV64D
open SP1Clean.Advance SP1Clean.TryStepReduction

/-- Every successful result of this action leaves the entire input state unchanged. -/
def ReadOnlyAt {α : Type} (source : SailState) (action : SailM α) : Prop :=
  ∀ value target, (runSail action) source = .ok value target → target = source

namespace ReadOnlyAt

/-- A known state-preserving run supplies a frame by determinism. -/
theorem of_run {α : Type} {source : SailState} {action : SailM α} {value : α}
    (ran : (runSail action) source = .ok value source) : ReadOnlyAt source action := by
  intro other target actual
  rw [ran] at actual
  cases actual
  rfl

/-- Pure results leave the state unchanged. -/
theorem pure {α : Type} (source : SailState) (value : α) :
    ReadOnlyAt source (Pure.pure value) := of_run rfl

/-- Sequential read-only actions compose at the same source. -/
theorem bind {α β : Type} {source : SailState} {action : SailM α} {next : α → SailM β}
    (first : ReadOnlyAt source action) (rest : ∀ value, ReadOnlyAt source (next value)) :
    ReadOnlyAt source (action >>= next) := by
  intro value target ran
  obtain ⟨middle, result, step, suffix⟩ := run_bind_success _ _ source target value ran
  obtain rfl := first result middle step
  exact rest result value target suffix

/-- A known prefix result selects the only reachable continuation. -/
theorem bind_of_run {α β : Type} {source : SailState} {action : SailM α} {next : α → SailM β}
    {value : α} (ran : (runSail action) source = .ok value source)
    (rest : ReadOnlyAt source (next value)) : ReadOnlyAt source (action >>= next) := by
  intro result target actual
  rw [run_bind_of_run source action value ran] at actual
  exact rest result target actual

/-- An underlying Sail exception has no successful result. -/
theorem throw {α : Type} (source : SailState) (error : Sail.Error exception) :
    ReadOnlyAt source (throw error : SailM α) := by
  intro value target ran
  rw [runSail_throw] at ran
  cases ran

end ReadOnlyAt

/-- An early-return action preserves state through every read-only continuation. This observes
only upstream execution, including exceptions and early returns. -/
def ReadOnlyEAt {α γ : Type} (source : SailState) (action : SailME γ α) : Prop :=
  ∀ next : α → SailME γ γ,
    (∀ value, ReadOnlyAt source (PreSail.PreSailME.run (next value))) →
    ReadOnlyAt source (PreSail.PreSailME.run (action >>= next))

/-- Lifting a read-only action preserves its frame in an early-return block. -/
theorem ReadOnlyAt.lift {α β : Type} {source : SailState} {action : SailM α}
    (frame : ReadOnlyAt source action) : ReadOnlyEAt source (liftM action : SailME β α) := by
  intro next rest
  rw [PreSail.PreSailME.run_lift_bind]
  exact frame.bind rest

namespace ReadOnlyEAt

/-- A pure expression passes its result to the read-only continuation. -/
theorem pure {α γ : Type} (source : SailState) (value : α) :
    ReadOnlyEAt source (Pure.pure value : SailME γ α) := by
  intro next rest
  simpa only [pure_bind] using rest value

/-- Early return preserves the state and skips the continuation. -/
theorem earlyReturn {α γ : Type} (source : SailState) (value : γ) :
    ReadOnlyEAt source (PreSail.PreSailME.throw value : SailME γ α) := by
  intro next _
  exact ReadOnlyAt.pure source value

/-- An underlying Sail exception cannot complete an early-return block successfully. -/
theorem throw {α γ : Type} (source : SailState) (error : Sail.Error exception) :
    ReadOnlyEAt source (throw error : SailME γ α) := by
  intro next _
  exact ReadOnlyAt.throw source error

/-- Early-return bind composes frames, including the short-circuiting branch. -/
theorem bindE {α β γ : Type} {source : SailState} {action : SailME γ α}
    {next : α → SailME γ β} (first : ReadOnlyEAt source action)
    (rest : ∀ value, ReadOnlyEAt source (next value)) :
    ReadOnlyEAt source (action >>= next) := by
  intro continuation frame
  rw [bind_assoc]
  exact first _ (fun value => rest value continuation frame)

/-- A known lifted result selects the reachable early-return continuation. -/
theorem bindE_of_run {α β γ : Type} {source : SailState} {action : SailM α}
    {next : α → SailME γ β} {value : α} (ran : runSail action source = .ok value source)
    (rest : ReadOnlyEAt source (next value)) :
    ReadOnlyEAt source ((liftM action : SailME γ α) >>= next) := by
  intro continuation frame
  rw [bind_assoc, PreSail.PreSailME.run_lift_bind]
  exact ReadOnlyAt.bind_of_run ran (rest continuation frame)

/-- Eliminating the early-return layer does not introduce state changes. -/
theorem runE {α : Type} {source : SailState} {action : SailME α α}
    (frame : ReadOnlyEAt source action) : ReadOnlyAt source (PreSail.PreSailME.run action) := by
  have result := frame Pure.pure (fun value => ReadOnlyAt.pure source value)
  simpa only [bind_pure] using result

/-- A bounded early-return loop preserves state whenever its body and condition do. -/
theorem untilE {α β : Type} (source : SailState) (fuel : ℕ) (condition : α → SailME β Bool)
    (initial : α) (body : α → SailME β α)
    (test : ∀ value, ReadOnlyEAt source (condition value))
    (step : ∀ value, ReadOnlyEAt source (body value)) :
    ReadOnlyEAt source (untilFuelM fuel condition initial body) := by
  unfold untilFuelM
  generalize fuel + 1 = remaining
  induction remaining generalizing initial with
  | zero => exact throw source (.Assertion "untilFuelM: termination limit reached")
  | succ fuel ih =>
    apply (step initial).bindE
    intro value
    apply (test value).bindE
    intro done
    cases done
    · exact ih value
    · exact pure source _

end ReadOnlyEAt
end SP1Clean.SailFrame
