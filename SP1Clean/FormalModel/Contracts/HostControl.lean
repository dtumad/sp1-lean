import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.BoundedWord

/-! # Native terminal and constrained-replay control calls

HALT accepts canonical exits below both the field characteristic and `2^32`. Its host handler
consumes the instruction handoff; the instruction itself remains the sole Exit sender.
ENTER_UNCONSTRAINED returns zero and VERIFY_SP1_PROOF returns its code. Both preserve the
host and guest memory in constrained replay.
Neither contract imposes a restriction on unused guest arguments.
-/

namespace SP1Clean.HostHaltChip

structure Inputs (F : Type) where
  call : HostCallChip.Message F
  comparison : Circuits.Types.LtOperationUnsigned F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def bound (p : ℕ) : ℕ := min p (2 ^ 32)

def CallSpec {p : ℕ} [Fact p.Prime] (call : HostCallChip.Message (ZMod p)) : Prop :=
  call.code = 0 ∧ call.result = 0 ∧ call.length = 0 ∧
    Word.isU64 call.arg1 ∧ Word.toNat call.arg1 < bound p

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop := CallSpec input.call

end SP1Clean.HostHaltChip

namespace SP1Clean.HostNoopChip

/-- Constrained-replay calls that preserve the complete host and have no guest-memory effects. -/
inductive Kind where
  | enter | verify
deriving DecidableEq

/-- Both handlers consume the complete instruction-authenticated host handoff. -/
abbrev Inputs := HostCallChip.Message

/-- Exact full-width syscall word, with all reserved bytes zero. -/
def codeWord {p : ℕ} (kind : Kind) : Word (ZMod p) :=
  match kind with
  | .enter => #v[3, 0, 0, 0]
  | .verify => #v[27, 0, 0, 0]

/-- ENTER clears x5. VERIFY retains the syscall code in x5. -/
def resultWord {p : ℕ} (kind : Kind) : Word (ZMod p) :=
  match kind with
  | .enter => 0
  | .verify => codeWord .verify

/-- No-effect calls leave both arguments unrestricted and use no WRITE length. -/
def Spec {p : ℕ} [Fact p.Prime] (kind : Kind) (input : Inputs (ZMod p)) : Prop :=
  input.code = codeWord kind ∧ input.result = resultWord kind ∧ input.length = 0

end SP1Clean.HostNoopChip
