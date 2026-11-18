import SP1Clean.Soundness.OrdinaryObservation
import SP1Clean.Native.Operations.OrdinaryObservationEndpoint
import ToClean.Air.HintIndex

/-! # The ordinary observation tables installed with the host inventory

Two physical tables join the host inventory: the ordered consumer of ordinary receipts and its
terminal, at the mode the supplied target fixes. The consumer's rows are demanded by receipts and
indexed by the receipt's clock; the guard checks the complete receipt, so a misrouted private row
cannot answer another receipt. The terminal's single row is demanded by the chain's final link.

The retirement flag and the mode are static data of the supplied source and target, so the
tables' names and channels are stated once for every value.
-/

namespace SP1Clean.Soundness.OrdinaryObservation

open Circuit Air.Flat Channels
open SP1Clean.OrdinaryObservation (Inputs Mode terminal terminalGeneration terminalName circuit)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Each ordinary receipt demands one consumer row, indexed by the receipt's clock. -/
def consumerDemand (enabled : Bool) : WitnessGeneration.DemandMode (ZMod p) Inputs where
  channel := InstructionReceipt.channel
  trigger := .push
  guard message :=
    Witgen.HintIndex.messageEq
      (Witgen.HintIndex.input (Input := Inputs) (circuit (p := p) enabled).name
        (message.clk_high.val * 16777216 + message.clk_low.val)).receipt message
  input message := pure (fromElements ((toElements (Witgen.HintIndex.input (Input := Inputs)
      (circuit (p := p) enabled).name (message.clk_high.val * 16777216 + message.clk_low.val))).map
    WitnessGeneration.Cell.witness))

/-- The ordered receipt consumer. -/
def consumer (enabled : Bool) : Component (ZMod p) :=
  (view (consumerDemand enabled) enabled).component

/-- The chain's terminal at a static mode. -/
def terminalComponent (mode : Mode) : Component (ZMod p) :=
  { circuit := terminal mode, generation := terminalGeneration, Assumptions := (terminal mode).Assumptions }

/-- Both observation tables, in installation order. -/
def tables (enabled : Bool) (mode : Mode) : List (Component (ZMod p)) :=
  [consumer enabled, terminalComponent mode]

theorem consumer_name (enabled : Bool) :
    (consumer (p := p) enabled).circuit.name = "sp1.native.ordinary_observation" := rfl

theorem terminal_name (mode : Mode) : (terminalComponent (p := p) mode).circuit.name = terminalName := by
  cases mode <;> rfl

/-- The consumer uses only the Byte channel, the receipt protocol and its observation links. -/
theorem consumer_channels (enabled : Bool) :
    (consumer (p := p) enabled).circuit.channels ⊆
      [byteChannel.toRaw, InstructionReceipt.channel.toRaw,
        SP1Clean.OrdinaryObservation.stateChannel.toRaw] :=
  SP1Clean.OrdinaryObservation.circuit_channels_subset enabled

/-- The terminal uses only the observation links. -/
theorem terminal_channels (mode : Mode) :
    (terminalComponent (p := p) mode).circuit.channels =
      [SP1Clean.OrdinaryObservation.stateChannel.toRaw, SP1Clean.OrdinaryObservation.stateChannel.toRaw] := by
  cases mode <;> rfl

end SP1Clean.Soundness.OrdinaryObservation
