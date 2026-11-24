import SP1Clean.Proofs.Operations.WriteBufferPhysical
import ToClean.Air.ChannelClosure

/-! # Original signed ledger for both native WRITE buffer tables

The span pulls its complete header, pushes a start and pulls a stop. Each active
word pulls its predecessor and its read receipt, and pushes its successor. Weights
are the actual row activity, including zeros on every disabled occurrence.
-/

namespace SP1Clean.WriteBuffer

open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_span_ends (env : Environment (ZMod p)) (s : Var Span (ZMod p)) :
    Eval.eval env s.source = (ProvableStruct.eval env s).source ∧
      Eval.eval env s.target = (ProvableStruct.eval env s).target := by
  rcases s with ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩
  simp only [Span.source, Span.target, circuit_norm, and_self]

omit [Fact (2 ^ 17 < p)] in
private theorem eval_step_ends (env : Environment (ZMod p)) (s : Var Step (ZMod p)) :
    Eval.eval env s.source = (ProvableStruct.eval env s).source ∧
      Eval.eval env s.target = (ProvableStruct.eval env s).target := by
  rcases s with ⟨⟨_, _, _⟩, _, _, _⟩
  simp only [Step.source, Step.target, circuit_norm, and_self]

private theorem span_end_values (s : Var Span (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((spanMain s).operations o).interactionValuesWith channel.toRaw env =
      [channel.pushedValue (ProvableStruct.eval env s).source, channel.pulledValue (ProvableStruct.eval env s).target] := by
  have raw : ((spanMain s).operations o).interactionsWith channel.toRaw = [(channel.pushed s.source).toRaw, (channel.pulled s.target).toRaw] := by
    rw [span_nonbyte _ _ _ (by simp [channel, byteChannel, circuit_norm])]
    simp [channel, WritePacket.channel, effectHeaderChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    (eval_span_ends env s).1, (eval_span_ends env s).2]

private theorem step_end_values (s : Var Step (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((stepMain s).operations o).interactionValuesWith channel.toRaw env =
      [channel.pulledValue (ProvableStruct.eval env s).source, channel.pushedValue (ProvableStruct.eval env s).target] := by
  have raw : ((stepMain s).operations o).interactionsWith channel.toRaw = [(channel.pulled s.source).toRaw, (channel.pushed s.target).toRaw] := by
    rw [step_nonbyte _ _ _ (by simp [channel, byteChannel, circuit_norm])]
    simp [channel, WriteProbe.readChannel, wordChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    (eval_step_ends env s).1, (eval_step_ends env s).2]

private theorem span_header_values (s : Var Span (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((spanMain s).operations o).interactionValuesWith WritePacket.channel.toRaw env = [WritePacket.channel.pulledValue (eval env s.header)] := by
  have raw : ((spanMain s).operations o).interactionsWith WritePacket.channel.toRaw = [(WritePacket.channel.pulled s.header).toRaw] := by
    rw [span_nonbyte _ _ _ (by simp [WritePacket.channel, byteChannel, circuit_norm])]
    simp [channel, WritePacket.channel, effectHeaderChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled]

private theorem span_effect_values (s : Var Span (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((spanMain s).operations o).interactionValuesWith effectHeaderChannel.toRaw env = [effectHeaderChannel.pushedValue (eval env s.header)] := by
  have raw : ((spanMain s).operations o).interactionsWith effectHeaderChannel.toRaw = [(effectHeaderChannel.pushed s.header).toRaw] := by
    rw [span_nonbyte _ _ _ (by simp [effectHeaderChannel, byteChannel, circuit_norm])]
    simp [channel, WritePacket.channel, effectHeaderChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed]

private theorem step_read_values (s : Var Step (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((stepMain s).operations o).interactionValuesWith WriteProbe.readChannel.toRaw env = [WriteProbe.readChannel.pulledValue (eval env s.read)] := by
  have raw : ((stepMain s).operations o).interactionsWith WriteProbe.readChannel.toRaw = [(WriteProbe.readChannel.pulled s.read).toRaw] := by
    rw [step_nonbyte _ _ _ (by simp [WriteProbe.readChannel, byteChannel, circuit_norm])]
    simp [channel, WriteProbe.readChannel, wordChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled]

private theorem step_word_values (s : Var Step (ZMod p)) (o : ℕ) (env : Environment (ZMod p)) :
    ((stepMain s).operations o).interactionValuesWith wordChannel.toRaw env = [wordChannel.pushedValue (eval env s.read)] := by
  have raw : ((stepMain s).operations o).interactionsWith wordChannel.toRaw = [(wordChannel.pushed s.read).toRaw] := by
    rw [step_nonbyte _ _ _ (by simp [wordChannel, byteChannel, circuit_norm])]
    simp [channel, WriteProbe.readChannel, wordChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed]

/-- Signed source/stop contributions of the actual guarded span row. -/
theorem span_cursors (input : Var SpanRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((spanComponent.circuit.main input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedIfValue (env input.2) (ProvableStruct.eval env input.1).source,
       channel.pulledIfValue (env input.2) (ProvableStruct.eval env input.1).target] := by
  change ((Guarded.main spanCircuit spanGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [spanCircuit, span_end_values, List.map_cons, List.map_nil, Channel.pushedValue,
    Channel.pulledValue, Channel.pushedIfValue, Channel.pulledIfValue, mul_one]

/-- Signed cursor edge of the actual guarded word row, retaining zero padding. -/
theorem word_cursors (input : Var WordRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((wordComponent.circuit.main input).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pulledIfValue (env input.2) (ProvableStruct.eval env input.1).source,
       channel.pushedIfValue (env input.2) (ProvableStruct.eval env input.1).target] := by
  change ((Guarded.main stepCircuit stepGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [stepCircuit, step_end_values, List.map_cons, List.map_nil, Channel.pushedValue,
    Channel.pulledValue, Channel.pushedIfValue, Channel.pulledIfValue, mul_one]

/-- Each enabled span consumes exactly one complete typed WRITE header. -/
theorem span_headers (input : Var SpanRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((spanComponent.circuit.main input).operations offset).interactionValuesWith WritePacket.channel.toRaw env =
      [WritePacket.channel.pulledIfValue (env input.2) (eval env input.1.header)] := by
  change ((Guarded.main spanCircuit spanGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [spanCircuit, span_header_values, List.map_cons, List.map_nil, Channel.pulledValue,
    Channel.pulledIfValue, mul_one]

/-- Every span emits its bound header, including an empty packet. -/
theorem span_effect_headers (input : Var SpanRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((spanComponent.circuit.main input).operations offset).interactionValuesWith effectHeaderChannel.toRaw env =
      [effectHeaderChannel.pushedIfValue (env input.2) (eval env input.1.header)] := by
  change ((Guarded.main spanCircuit spanGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [spanCircuit, span_effect_values, List.map_cons, List.map_nil, Channel.pushedValue,
    Channel.pushedIfValue, mul_one]

/-- Each enabled word consumes exactly one full read receipt from the observation table. -/
theorem word_reads (input : Var WordRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((wordComponent.circuit.main input).operations offset).interactionValuesWith WriteProbe.readChannel.toRaw env =
      [WriteProbe.readChannel.pulledIfValue (env input.2) (eval env input.1.read)] := by
  change ((Guarded.main stepCircuit stepGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [stepCircuit, step_read_values, List.map_cons, List.map_nil, Channel.pulledValue,
    Channel.pulledIfValue, mul_one]

/-- Every word emits its authenticated read verbatim to the effect receiver. -/
theorem word_values (input : Var WordRow (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((wordComponent.circuit.main input).operations offset).interactionValuesWith wordChannel.toRaw env =
      [wordChannel.pushedIfValue (env input.2) (eval env input.1.read)] := by
  change ((Guarded.main stepCircuit stepGuardSupported input).operations offset).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  simp only [stepCircuit, step_word_values, List.map_cons, List.map_nil, Channel.pushedValue,
    Channel.pushedIfValue, mul_one]

end SP1Clean.WriteBuffer
