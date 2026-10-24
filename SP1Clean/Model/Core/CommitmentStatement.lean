module

public import SP1Clean.Model.Core.SyscallCode
public import SP1Clean.Model.Machine.EventExecution

/-! # Immutable commitments in an execution statement

Low-level COMMIT calls declare words of one public digest. The operational host may update
its recording arrays, but a provable execution's declarations must agree with its statement.
Repeated identical declarations are permitted. Neither a flag nor agreement implies that every
word was declared; coverage is a separate program property. This contract uses semantic events
and contains no circuit rows, witness readiness or compiler conditions.
-/

@[expose] public section

namespace SP1Clean.Model.Core

open Machine

/-- The two immutable digests and the flags advertised by a public statement. -/
structure CommitmentStatement where
  /-- Eight public-output words. -/
  committed : Vector (BitVec 32) 8
  /-- Eight deferred-proof words, canonical under `WellFormed`. -/
  deferred : Vector (BitVec 32) 8
  /-- The public-output commitment flag. -/
  commit : Bool
  /-- The deferred-proof commitment flag. -/
  commitDeferred : Bool
deriving DecidableEq, Repr, Inhabited

namespace CommitmentStatement

/-- Deferred words are canonical field elements; public-output words are ordinary u32s. -/
def WellFormed (statement : CommitmentStatement) (characteristic : ℕ) : Prop :=
  ∀ index : Fin 8, statement.deferred[index].toNat < characteristic

/-- Select the bank named by the concrete commitment syscall. -/
def bank (statement : CommitmentStatement) (deferred : Bool) : Vector (BitVec 32) 8 :=
  if deferred then statement.deferred else statement.committed

/-- A declaration sets its rolling flag and agrees with the selected immutable word. -/
def MatchesDeclaration (statement : CommitmentStatement) (deferred : Bool)
    (event : CoreSyscallEvent) : Prop :=
  event.rawCode = (if deferred then SyscallKind.commitDeferred else .commit).code →
    (if deferred then statement.commitDeferred else statement.commit) = true ∧
      ∃ index : Fin 8, event.arg1 = BitVec.ofNat 64 index.val ∧
        event.arg2 = ((statement.bank deferred)[index]).setWidth 64

/-- Ordinary instructions and other host calls impose no commitment declaration. -/
def MatchesEvent (statement : CommitmentStatement) : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall event =>
      statement.MatchesDeclaration false event ∧ statement.MatchesDeclaration true event

/-- Every actual declaration agrees; this does not assert that a declaration exists. -/
def Matches (statement : CommitmentStatement) (events : List ExecutionEvent) : Prop :=
  ∀ event ∈ events, statement.MatchesEvent event

instance (statement : CommitmentStatement) (characteristic : ℕ) :
    Decidable (statement.WellFormed characteristic) := by
  unfold WellFormed
  infer_instance

instance (statement : CommitmentStatement) (deferred : Bool) (event : CoreSyscallEvent) :
    Decidable (statement.MatchesDeclaration deferred event) := by
  unfold MatchesDeclaration
  infer_instance

instance (statement : CommitmentStatement) (event : ExecutionEvent) :
    Decidable (statement.MatchesEvent event) := by
  cases event <;> unfold MatchesEvent <;> infer_instance

instance (statement : CommitmentStatement) (events : List ExecutionEvent) :
    Decidable (statement.Matches events) := by
  unfold Matches
  infer_instance

@[simp] theorem matches_nil (statement : CommitmentStatement) : statement.Matches [] := by
  simp [Matches]

@[simp] theorem matches_cons (statement : CommitmentStatement) (event : ExecutionEvent)
    (events : List ExecutionEvent) :
    statement.Matches (event :: events) ↔ statement.MatchesEvent event ∧ statement.Matches events := by
  simp [Matches]

/-- One immutable statement is preserved when adjacent segments are composed. -/
theorem matches_append (statement : CommitmentStatement) (first second : List ExecutionEvent) :
    statement.Matches (first ++ second) ↔ statement.Matches first ∧ statement.Matches second := by
  simp [Matches, List.mem_append, or_imp, forall_and]

/-- Restricting a segment cannot introduce a conflicting declaration. -/
theorem matches_sublist {statement : CommitmentStatement} {part events : List ExecutionEvent}
    (agreement : statement.Matches events) (subset : part.Sublist events) : statement.Matches part :=
  fun event member => agreement event (subset.subset member)

/-- Both sides of any local cut keep the same immutable commitment statement. -/
theorem matches_split {statement : CommitmentStatement} {events : List ExecutionEvent}
    (agreement : statement.Matches events) (cut : ℕ) :
    statement.Matches (events.take cut) ∧ statement.Matches (events.drop cut) := by
  exact ⟨matches_sublist agreement (List.take_sublist cut events),
    matches_sublist agreement (List.drop_sublist cut events)⟩

end CommitmentStatement
end SP1Clean.Model.Core
