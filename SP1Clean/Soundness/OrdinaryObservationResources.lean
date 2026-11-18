import SP1Clean.Native.Operations.OrdinaryObservation
import SP1Clean.Native.Operations.OrdinaryObservationBoundary
import ToClean.Air.HintIndex

/-! # The ordinary observation tables installed with the host inventory

Four physical tables join the host inventory, none with a parameter: the ordered consumer of
ordinary receipts and one terminal per mode. The consumer's rows are demanded by receipts and
indexed by the receipt's clock; its guard checks the complete receipt, so a misrouted private row
cannot answer another receipt. A terminal's single row is demanded by the chain's final link. The
retirement flag rides in the chain, and the verifier pulls only the sentinel of the mode the target
fixes, so the same four tables serve every source and target.
-/

namespace SP1Clean.Soundness.OrdinaryObservation

open Circuit Air.Flat Channels
open SP1Clean.OrdinaryObservation (Inputs Mode terminal terminalGeneration terminalName circuit)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Each ordinary receipt demands one consumer row, indexed by the receipt's clock. -/
def consumerDemand : WitnessGeneration.DemandMode (ZMod p) Inputs where
  channel := InstructionReceipt.channel
  trigger := .push
  guard message :=
    Witgen.HintIndex.messageEq
      (Witgen.HintIndex.input (Input := Inputs) (circuit (p := p)).name
        (message.clk_high.val * 16777216 + message.clk_low.val)).receipt message
  input message := pure (fromElements ((toElements (Witgen.HintIndex.input (Input := Inputs)
      (circuit (p := p)).name (message.clk_high.val * 16777216 + message.clk_low.val))).map
    WitnessGeneration.Cell.witness))

/-- The ordered receipt consumer. -/
def consumer : Component (ZMod p) :=
  { circuit := circuit, generation := .demand consumerDemand, Assumptions := circuit.Assumptions }

/-- The chain's terminal for one mode. -/
def terminalComponent (mode : Mode) : Component (ZMod p) :=
  { circuit := terminal mode, generation := terminalGeneration mode, Assumptions := (terminal mode).Assumptions }

/-- All four observation tables, in installation order. -/
def tables : List (Component (ZMod p)) :=
  [consumer, terminalComponent .empty, terminalComponent .nonempty, terminalComponent .any]

theorem consumer_name : (consumer (p := p)).circuit.name = "sp1.native.ordinary_observation" := rfl

theorem terminal_name (mode : Mode) :
    (terminalComponent (p := p) mode).circuit.name = terminalName mode := by
  cases mode <;> rfl

/-- The consumer uses only the Byte channel, the receipt protocol and its observation links. -/
theorem consumer_channels :
    (consumer (p := p)).circuit.channels ⊆
      [byteChannel.toRaw, InstructionReceipt.channel.toRaw,
        SP1Clean.OrdinaryObservation.stateChannel.toRaw] :=
  SP1Clean.OrdinaryObservation.circuit_channels_subset

/-- A terminal uses only the observation links. -/
theorem terminal_channels (mode : Mode) :
    (terminalComponent (p := p) mode).circuit.channels =
      [SP1Clean.OrdinaryObservation.stateChannel.toRaw, SP1Clean.OrdinaryObservation.stateChannel.toRaw] := by
  cases mode <;> rfl

end SP1Clean.Soundness.OrdinaryObservation
