module

public import SP1Clean.Model.Core.CommitmentStatement
public import SP1Clean.Model.Semantics.Decode
public import ToClean.Circuit.StaticTable

/-! # Immutable commitment declarations

A declaration identifies a bank and slot and carries the complete 32-bit word and rolling flag.
The channel is independent of a particular statement; its sole provider fixes all sixteen rows
from verifier-owned instance data. Membership authenticates each actual declaration without
requiring every slot to occur, or inferring occurrence from a flag.
-/

@[expose] public section

namespace SP1Clean.CommitmentDeclaration

open Circuit Model.Core

/-- One immutable bank/slot declaration with its public flag. -/
structure Row (F : Type) where
  /-- Zero selects public output; one selects deferred proofs. -/
  deferred : F
  /-- The slot index, from zero through seven. -/
  slot : F
  /-- The complete word, including its zero upper limbs. -/
  value : Word F
  /-- The selected bank's public commitment flag. -/
  flag : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Row

/-- Active calls request declarations from the single fixed source. -/
def channel {p : ℕ} : Channel (ZMod p) Row where
  name := "sp1.native.commitment_declaration"
  Guarantees _ _ := True

/-- Canonical request from an active commitment call. -/
def request {p : ℕ} (deferred : Bool) (slot : Fin 8)
    (value : Var Word (ZMod p)) : Var Row (ZMod p) :=
  ⟨.const (if deferred then 1 else 0), .const (slot.val : ℕ), value, 1⟩

/-- A row fixed by the public statement, including its actual rolling flag. -/
def encode {p : ℕ} [Fact p.Prime] (statement : CommitmentStatement) (deferred : Bool) (slot : Fin 8) : Row (ZMod p) :=
  ⟨(if deferred then 1 else 0 : ℕ), (slot.val : ℕ),
    Soundness.Target.bitVecToWord (((statement.bank deferred)[slot]).setWidth 64),
    (if (if deferred then statement.commitDeferred else statement.commit) then 1 else 0)⟩

/-- Both complete banks are fixed even when an execution declares only a subset of slots. -/
def rows {p : ℕ} [Fact p.Prime] (statement : CommitmentStatement) : List (Row (ZMod p)) :=
  List.ofFn (encode statement false) ++ List.ofFn (encode statement true)

/-- The complete immutable inventory supplied to Clean's fixed-table provider. -/
def table {p : ℕ} [Fact p.Prime] (statement : CommitmentStatement) : StaticTable (ZMod p) Row :=
  .ofRows "sp1.native.commitment_declaration" (rows statement)

end SP1Clean.CommitmentDeclaration
