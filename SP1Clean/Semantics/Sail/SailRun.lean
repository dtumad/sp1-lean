import LeanRV64D.Defs
import Sail.ArchSemSequential

/-! # Sequential execution of the generated Sail model

SP1 uses the upstream ArchSem sequential state and interpreter. `runSail` specializes that
interpreter to the generated RISC-V architecture; the effect handlers and deterministic finite
choice policy remain owned by lean-sail.
-/

/-- The complete upstream sequential state for the generated RISC-V register family. -/
abbrev SailState := Sail.ArchSem.SequentialState LeanRV64D.RegisterType

namespace SP1Clean

/-- Execute a generated Sail action through the upstream sequential interpreter. -/
def runSail {α : Type} (action : LeanRV64D.SailM α) (state : SailState) :
    EStateM.Result (Sail.Error LeanRV64D.exception) SailState α :=
  (Sail.ArchSem.interpretSailEffects action).run state

@[simp] theorem runSail_pure {α : Type} (value : α) (state : SailState) :
    runSail (pure value) state = .ok value state := rfl

@[simp] theorem runSail_bind {α β : Type} (action : LeanRV64D.SailM α)
    (next : α → LeanRV64D.SailM β) (state : SailState) :
    runSail (action >>= next) state =
      match runSail action state with
      | .ok value target => runSail (next value) target
      | .error error target => .error error target := by
  unfold runSail
  rw [Sail.ArchSem.interpretSailEffects_bind]
  simp only [bind, EStateM.bind, EStateM.run]
  cases Sail.ArchSem.interpretSailEffects action state <;> rfl

/-- Mapping a returned value preserves the interpreted state and errors. -/
@[simp] theorem runSail_map {α β : Type} (f : α → β) (action : LeanRV64D.SailM α)
    (state : SailState) :
    runSail (f <$> action) state =
      match runSail action state with
      | .ok value target => .ok (f value) target
      | .error error target => .error error target := by
  rw [map_eq_pure_bind, runSail_bind]
  cases runSail action state <;> rfl

@[simp] theorem runSail_throw {α : Type} (error : Sail.Error LeanRV64D.exception)
    (state : SailState) : runSail (throw error : LeanRV64D.SailM α) state = .error error state := rfl

open LeanRV64D Sail Sail.ArchSem


/-- A successful action determines the state and value supplied to its continuation. -/
theorem runSail_bind_eq {α β : Type} (action : SailM α) (next : α → SailM β)
    (state target : SailState) (value : α) (h : runSail action state = .ok value target) :
    runSail (action >>= next) state = runSail (next value) target := by
  simp only [runSail_bind, h]

namespace SailEarlyReturn

/-- Normal completion of an action in an early-return block, observed through every remaining
continuation of that block. Early returns and errors still use the upstream interpreter. -/
def ContinuesWith {γ α : Type} (action : SailME γ α) (state : SailState)
    (value : α) (target : SailState) : Prop :=
  ∀ next : α → SailME γ γ,
    runSail (PreSail.PreSailME.run (action >>= next)) state = runSail (PreSail.PreSailME.run (next value)) target

/-- Sequencing two normally completing parts of an early-return block. -/
theorem ContinuesWith.bind {γ α β : Type} {action : SailME γ α} {next : α → SailME γ β}
    {state middle target : SailState} {value : α} {result : β}
    (h : ContinuesWith action state value middle)
    (hn : ContinuesWith (next value) middle result target) :
    ContinuesWith (action >>= next) state result target := by
  intro rest
  rw [bind_assoc, h, hn]

/-- A pure expression completes normally without changing the state. -/
theorem ContinuesWith.pure {γ α : Type} (value : α) (state : SailState) :
    ContinuesWith (pure value : SailME γ α) state value state := by
  intro next
  rw [pure_bind]

/-- A successful ordinary Sail action completes normally when lifted into an early-return block. -/
theorem ContinuesWith.lift {γ α : Type} {action : SailM α} {state target : SailState} {value : α}
    (h : runSail action state = .ok value target) :
    ContinuesWith (liftM action : SailME γ α) state value target := by
  intro next
  simp only [PreSail.PreSailME.run_lift_bind, runSail_bind, h]

/-- Completing a block with its normal result yields the corresponding upstream execution. -/
theorem ContinuesWith.run {γ : Type} {action : SailME γ γ} {state target : SailState} {value : γ}
    (h : ContinuesWith action state value target) :
    runSail (PreSail.PreSailME.run action) state = .ok value target := by
  simpa only [bind_pure, PreSail.PreSailME.run_pure, runSail_pure] using h Pure.pure

end SailEarlyReturn
end SP1Clean
