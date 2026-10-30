import SP1Clean.Proofs.Chips.HostCommitChip.Formal

/-! # Commitment calls on the actual Clean ledger

Each row consumes one instruction handoff, replaces one bank state, and supplies the original
instruction's historical PublicValues entries. Byte checks remain internal subcircuits.
These projections do not supply the bank's initial/final endpoints or prove global balance.
-/

namespace SP1Clean.HostCommitChip

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Guarding preserves the complete HostCall occurrence at its physical activity. -/
theorem guarded_host_values (deferred : Bool) (slot : Fin 8) (input : Var RowInput (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    (((circuit deferred slot).main input).operations offset).interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledIfValue (env input.2) (Eval.eval env input.1.call)] := by
  change ((Guarded.main (activeCircuit deferred slot) (guardSupported deferred slot) input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [activeCircuit, host_values, List.map_cons, List.map_nil,
    Channel.pulledValue, Channel.pulledIfValue, mul_neg, mul_one]

/-- An active row requests its slot's declaration; padding requests it at zero multiplicity. -/
theorem guarded_declaration_values (deferred : Bool) (slot : Fin 8) (input : Var RowInput (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    (((circuit deferred slot).main input).operations offset).interactionValuesWith
        CommitmentDeclaration.channel.toRaw env =
      [CommitmentDeclaration.channel.pulledIfValue (env input.2)
        (Eval.eval env (CommitmentDeclaration.request deferred slot input.1.call.arg2))] := by
  change ((Guarded.main (activeCircuit deferred slot) (guardSupported deferred slot) input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [activeCircuit, declaration_values, List.map_cons, List.map_nil,
    Channel.pulledValue, Channel.pulledIfValue, mul_neg, mul_one]

/-- Both bank-state occurrences survive padding at zero multiplicity. -/
theorem guarded_state_values (deferred : Bool) (slot : Fin 8) (input : Var RowInput (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    (((circuit deferred slot).main input).operations offset).interactionValuesWith (stateChannel deferred).toRaw env =
      [(stateChannel deferred).pulledIfValue (env input.2) (Eval.eval env input.1.previous),
       (stateChannel deferred).pushedIfValue (env input.2) (Eval.eval env (input.1.next slot))] := by
  change ((Guarded.main (activeCircuit deferred slot) (guardSupported deferred slot) input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [activeCircuit, state_values, List.map_cons, List.map_nil,
    Channel.pulledValue, Channel.pushedValue, Channel.pulledIfValue, Channel.pushedIfValue,
    mul_neg, mul_one]

end SP1Clean.HostCommitChip
