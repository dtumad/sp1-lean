import ToClean.Air.ChannelClosure
import SP1Clean.Proofs.Chips.WritePacket.Ledger
import ToClean.Circuit.EmittedInteraction

/-! # The three signed physical receipts of every guarded WRITE packet row -/

namespace SP1Clean.WritePacket
open Circuit Air.Flat
open scoped Classical
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Physical packet input paired with its activity cell. -/
abbrev Row := ProvablePair Inputs field

/-- These are precisely the three signed occurrences of a physical packet row, including padding. -/
def rowTraffic (r : Row (ZMod p)) : List (Interaction (ZMod p)) :=
  [HostCallChip.channel.pulledIfValue r.2 r.1.call, WriteProbe.readChannel.pulledIfValue r.2 r.1.read,
    channel.pushedIfValue r.2 r.1.header]

/-- The emitted call, x12 length request and header are all computed from the same public row cells. -/
theorem component_traffic (env : Environment (ZMod p)) : component.operations.interactionValues env =
    rowTraffic (valueFromOffset Row 0 env) := by
  let input := varFromOffset Row 0 (F := ZMod p)
  rw [Operations.interactionValues, Component.interactions_eq]
  change ((((Guarded.main circuit guardSupported input).operations (size Row)).interactions).map _) = _
  rw [Guarded.main_interactions]
  change (((((main input.1).operations (size Row)).interactions.map _).map _)) = _
  rw [main_interactions]
  have decode (v : Var Row (ZMod p)) :
      eval env v.1.call = (eval env v).1.call ∧ eval env v.1.read = (eval env v).1.read ∧
      eval env v.1.header = (eval env v).1.header := by
    simp only [Inputs.call, Inputs.read, Inputs.header, ClockParts.address, ClockParts.low24, ClockParts.high24, circuit_norm, and_self]
  simp only [List.map_cons, List.map_nil, AbstractInteraction.eval_guard, Channel.eval_pulled, Channel.eval_pushed,
    Channel.pulledValue, Channel.pushedValue, Channel.pulledIfValue, Channel.pushedIfValue, mul_one, Guarded.eval_activity,
    (decode input).1, (decode input).2.1, (decode input).2.2, input, eval_varFromOffset_valueFromOffset, rowTraffic]

/-- Complete packet header emitted at the original physical activity. -/
theorem header_at (env : Environment (ZMod p)) :
    let r := valueFromOffset Row 0 env
    component.operations.interactionValuesWith channel.toRaw env = [channel.pushedIfValue r.2 r.1.header] := by
  rw [Operations.interactionValuesWith_eq_filter,component_traffic]
  simp [rowTraffic,Channel.pushedIfValue,Channel.pulledIfValue,HostCallChip.channel,WriteProbe.readChannel,channel,Channel.toRaw]

/-- Actual packet lookup for the complete x12 word, including its incoming ECALL clock. -/
theorem read_at (env : Environment (ZMod p)) :
    let r := valueFromOffset Row 0 env
    component.operations.interactionValuesWith WriteProbe.readChannel.toRaw env = [WriteProbe.readChannel.pulledIfValue r.2 r.1.read] := by
  rw [Operations.interactionValuesWith_eq_filter,component_traffic]
  simp [rowTraffic,Channel.pushedIfValue,Channel.pulledIfValue,HostCallChip.channel,WriteProbe.readChannel,channel,Channel.toRaw]

/-- Active packets tie their underlying HostCall's 24-bit clock to the same x12 read cut. -/
theorem packet_valid_at (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    let r := valueFromOffset Row 0 env
    IsBool r.2 ∧ (r.2 = 1 → Spec r.1) := by
  have assumed : component.CircuitAssumptions env := fun _ => trivial
  apply (Component.weakSoundness assumed checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (component.inChannelsOrGuarantees env)]
  intro ch member
  change ch ∈ [HostCallChip.channel.toRaw,WriteProbe.readChannel.toRaw] at member
  rcases List.mem_cons.mp member with rfl | last
  · exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel,Channel.toRaw]) _ _
  · obtain rfl := List.mem_singleton.mp last
    exact Operations.channelGuarantees_of_trivial _ (by simp [WriteProbe.readChannel,Channel.toRaw]) _ _

end SP1Clean.WritePacket
