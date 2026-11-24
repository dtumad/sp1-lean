import SP1Clean.Proofs.Chips.WritePacket.Ledger
import SP1Clean.Proofs.Operations.WriteBufferLedger
import ToClean.Air.Authentication

/-! # Physical consumers of the native WRITE read receipt

Both length and buffer-word rows issue one Boolean-gated pull. In particular no malformed
multiplicity on the pull side can fund a different consumer under field-sum balance.
-/

namespace SP1Clean

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime]

private theorem boolean_pull {R : TypeMap} [ProvableType R] (ch : Channel (ZMod p) R)
    (msg : R (ZMod p)) (gate : ZMod p) (boolean : IsBool gate) :
    (ch.pulledIfValue gate msg).mult = 0 ∨ (ch.pulledIfValue gate msg).Pull := by
  rcases boolean with off | on
  · exact Or.inl off
  · exact Or.inr ⟨rfl, on⟩

namespace WritePacket

variable [Fact (2 ^ 24 < p)]

private theorem length_values (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main input).operations offset).interactionValuesWith WriteProbe.readChannel.toRaw env =
      [WriteProbe.readChannel.pulledValue (eval env input.read)] := by
  have raw : ((main input).operations offset).interactionsWith WriteProbe.readChannel.toRaw =
      [(WriteProbe.readChannel.pulled input.read).toRaw] := by
    rw [Operations.interactionsWith, main_interactions]
    simp [WriteProbe.readChannel, HostCallChip.channel, channel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled]

/-- The actual x12 length read and its physical gate. -/
theorem length_read (input : Var (ProvablePair Inputs field) (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((guarded.main input).operations offset).interactionValuesWith WriteProbe.readChannel.toRaw env =
      [WriteProbe.readChannel.pulledIfValue (env input.2) (eval env input.1.read)] := by
  change ((Guarded.main circuit guardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [circuit, length_values, List.map_cons, List.map_nil, Channel.pulledValue, Channel.pulledIfValue, mul_one]

/-- A checked WRITE packet row consumes a length read and cannot publish one. -/
theorem no_read_push (property : WriteProbe.Read (ZMod p) → Prop) :
    component.Authenticates WriteProbe.readChannel property := by
  apply Component.Authenticates.of_pulls
  intro env checked occurrence member
  let vars := varFromOffset (ProvablePair Inputs field) 0 (F := ZMod p)
  let offset := size (ProvablePair Inputs field)
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change occurrence ∈ ((guarded.main vars).operations offset).interactionValuesWith _ env at member
  rw [length_read] at member
  obtain rfl := List.mem_singleton.mp member
  apply boolean_pull
  exact Guarded.activity_of_constraints circuit guardSupported vars offset env ((Component.constraintsHold_iff env).mp checked)

end WritePacket

namespace WriteBuffer

variable [Fact (2 ^ 17 < p)]

/-- A checked aligned-word row consumes a RAM read and cannot publish one. -/
theorem no_read_push (property : WriteProbe.Read (ZMod p) → Prop) :
    wordComponent.Authenticates WriteProbe.readChannel property := by
  apply Component.Authenticates.of_pulls
  intro env checked occurrence member
  let vars := varFromOffset WordRow 0 (F := ZMod p)
  let offset := size WordRow
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change occurrence ∈ ((wordComponent.circuit.main vars).operations offset).interactionValuesWith _ env at member
  rw [word_reads] at member
  obtain rfl := List.mem_singleton.mp member
  apply boolean_pull
  exact Guarded.activity_of_constraints stepCircuit stepGuardSupported vars offset env ((Component.constraintsHold_iff env).mp checked)

end WriteBuffer
end SP1Clean
