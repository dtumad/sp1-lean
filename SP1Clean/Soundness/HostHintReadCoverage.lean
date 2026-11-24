import SP1Clean.Soundness.HintReadCoverage
import ToClean.Air.HintIndex
import SP1Clean.Proofs.Chips.HostHintReadChip.Bridge
import SP1Clean.Proofs.Chips.HostHintReadChip.Guarded

/-! # HINT_READ coverage with the actual handler endpoints

The word walk now starts and ends at the handler's physical interactions. Authenticated current
queue and immutable records identify its exact node and padded count. The enclosing shard must
still derive these record bindings, local specifications, and each call's projected balance.
-/

namespace SP1Clean.Soundness.HostHintReadCoverage

open Circuit Air.Flat Semantics Semantics.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The registered demand-padded HINT_READ handler. -/
abbrev handler : Component (ZMod p) := HostHintReadChip.component

/-- Physical activity of the HINT_READ row. -/
def activity : Expression (ZMod p) := (varFromOffset HostHintReadChip.RowInput 0).2

/-- Active handler row environments, retaining their original physical order and data. -/
def activeEnvs (table : Table (ZMod p)) (data : ProverData (ZMod p)) :=
  (table.table.map (Environment.fromArray · data)).filter (fun env => decide (env activity = 1))

def input (env : Environment (ZMod p)) : HostHintReadChip.Inputs (ZMod p) :=
  (valueFromOffset HostHintReadChip.RowInput 0 env).1

omit [Fact (2 ^ 25 < p)] in
theorem decoded_input (env : Environment (ZMod p)) :
    eval env (varFromOffset (F := ZMod p) HostHintReadChip.RowInput 0).1 = input env := by
  have decode := eval_varFromOffset_valueFromOffset HostHintReadChip.RowInput 0 env
  rw [CircuitType.eval_var_provablePair] at decode
  exact congrArg Prod.fst decode

omit [Fact (2 ^ 25 < p)] in
theorem decoded_activity (env : Environment (ZMod p)) :
    env activity = (valueFromOffset HostHintReadChip.RowInput 0 env).2 := by
  rw [← eval_varFromOffset_valueFromOffset HostHintReadChip.RowInput 0 env]
  exact Guarded.eval_activity env (varFromOffset HostHintReadChip.RowInput 0)

theorem active_spec (env : Environment (ZMod p)) (valid : handler.Spec env) (enabled : env activity = 1) :
    HostHintReadChip.Spec (input env) := by
  change IsBool (valueFromOffset HostHintReadChip.RowInput 0 env).2 ∧
    ((valueFromOffset HostHintReadChip.RowInput 0 env).2 = 1 → HostHintReadChip.Spec (input env)) at valid
  exact valid.2 ((decoded_activity env).symm.trans enabled)

theorem handler_cursor (env : Environment (ZMod p)) :
    handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env =
      [HintReadWordChip.stateChannel.pushedIfValue (env activity) (input env).first,
       HintReadWordChip.stateChannel.pulledIfValue (env activity) (input env).final] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((Guarded.main HostHintReadChip.circuit inferInstance (varFromOffset HostHintReadChip.RowInput 0)).operations
    (size HostHintReadChip.RowInput)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((HostHintReadChip.main (varFromOffset HostHintReadChip.RowInput 0).1).operations (size HostHintReadChip.RowInput)).interactionValuesWith HintReadWordChip.stateChannel.toRaw env).map _ = _
  rw [HostHintReadChip.cursor_values, decoded_input]
  simp [activity,Channel.pushedValue,Channel.pulledValue,Channel.pushedIfValue,Channel.pulledIfValue]

/-- Physical cursor balance requires every word of the handler's actual current hint exactly once. -/
theorem complete_indices (env : Environment (ZMod p)) (rows : List (HintReadCoverage.Row (p := p)))
    (valid : handler.Spec env) (enabled : env activity = 1)
    (wordSpecs : HintReadCoverage.Steps rows)
    (balanced : BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        HintReadCoverage.interactions rows HintReadWordChip.stateChannel.toRaw))
    (store : Store) (hints : List Bytes) (current : (input env).previous.Binds store hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store) :
    ∃ bytes rest, hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      ((HintReadCoverage.activeRows rows).map
        fun row => Address.toNat (HintReadCoverage.rowInput row).index).Perm
          (List.range (wordCount bytes)) := by
  obtain ⟨node, rest, _, head, next, _, count⟩ :=
    HostHintReadChip.node_effect_of_spec (input env) (active_spec env valid enabled) store hints current header ending
  rw [handler_cursor,enabled] at balanced
  rw [HintReadCoverage.cursor_interactions] at balanced
  have inventory := HintReadCoverage.complete_indices
    rows (input env).first (input env).final
    wordSpecs balanced (by simp [HostHintReadChip.Inputs.first, Address.toNat])
  change _ = _ at count
  change List.Perm _ (List.range (Address.toNat (input env).span.count)) at inventory
  rw [count] at inventory
  exact ⟨node.bytes, rest, head, next, inventory⟩

end SP1Clean.Soundness.HostHintReadCoverage
