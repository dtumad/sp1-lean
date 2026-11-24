import SP1Clean.Proofs.Chips.WritePacket.Ledger
import SP1Clean.Soundness.HostLocalHandoff

/-! # Exact HostCall dispatch with the native WRITE receiver

The active WRITE packet table consumes each complete released call at its physical clock.
Combining its signed physical ledger with the original supervisor's ledger closes a single
CPU-to-receiver permutation over all eight host calls.
-/

namespace SP1Clean.WritePacket

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem call_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith HostCallChip.channel.toRaw = [(HostCallChip.channel.pulled input.call).toRaw] := by
  rw [Operations.interactionsWith, main_interactions]
  simp [ChannelInteraction.toRaw, HostCallChip.channel, WriteProbe.readChannel, channel, Channel.toRaw]

/-- A packet row consumes its full HostCall payload exactly when its physical gate is active. -/
def receiver : ReceiverView (HostCallChip.channel (p := p)) where
  component := component
  activity := (varFromOffset (ProvablePair Inputs field) 0).2
  message env := eval env (varFromOffset (ProvablePair Inputs field) 0).1.call
  activity_of_constraints env checked := by
    rw [Component.constraintsHold_iff] at checked
    exact Guarded.activity_of_constraints circuit guardSupported _ (size (ProvablePair Inputs field)) env checked
  interactions env := by
    let input := varFromOffset (F := ZMod p) (ProvablePair Inputs field) 0
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change (((Guarded.main circuit guardSupported input).operations (size (ProvablePair Inputs field))).interactionsWith _).map _ = _
    rw [Guarded.main_interactionsWith]
    change (((((main input.1).operations (size (ProvablePair Inputs field))).interactionsWith HostCallChip.channel.toRaw).map _).map _) = _
    rw [call_interactions]
    simp only [List.map_cons, List.map_nil, AbstractInteraction.eval_guard, Channel.eval_pulled,
      Channel.pulledValue, Channel.pulledIfValue, mul_one]
    rfl

attribute [local instance] Soundness.cleanBalanceDecidableEq

/-- Removing zero-weight padding yields precisely the typed active packet calls. -/
theorem active_call_ledger (table : Table (ZMod p)) (installed : table.component = component) (checked : table.Constraints) :
    (table.interactionsWith HostCallChip.channel.toRaw).filter (fun i => decide (i.mult ≠ 0)) =
      (ReceiverView.tableMessages receiver table).map HostCallChip.channel.pulledValue := by
  have ledger := ReceiverView.messages_interactions [receiver] [table] (.cons (by change component = table.component; exact installed.symm) .nil)
    (fun t member => List.mem_singleton.mp member ▸ checked)
  rw [ReceiverView.messages_cons] at ledger
  simpa only [List.flatMap_cons, List.flatMap_nil, show ReceiverView.messages (channel := HostCallChip.channel (p := p)) [] [] = [] from rfl,
    List.append_nil] using ledger

end SP1Clean.WritePacket
