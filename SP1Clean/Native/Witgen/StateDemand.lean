module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Model.Channels
public import Clean.Air.WitnessGeneration.Generation
public import Clean.Circuit.WitnessIRSugar

/-! # State-driven instruction inputs

Clean creates one instruction row for each outstanding State push. Each component reads its
typed input from a named hint table and accepts a request only when the hinted row is active
and its entire incoming State message matches. The circuit still checks every hinted value.

Hint rows are indexed by eight-clock slots relative to the two-cell `sp1.state.origin` hint
(high clock, low clock). Gaps contain zero inputs. Relative indexing supports segments starting
at arbitrary clocks without allocating a prefix from clock zero. The origin is only an indexing
hint; it adds no semantic assumption. Invalid or missing hints fail routing or circuit checks.

This is input metadata for Clean's scheduler and emitter, not a second execution engine or a
completeness proof for witness generation. Execution rows deliberately have no multiplicity cell:
two equal requests produce two physical rows.
-/

@[expose] public section

namespace SP1Clean.Native.Witgen

open Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime]
variable {Input : TypeMap} [ProvableType Input]

/-- Relative eight-clock slot in the instruction hint inventory. UInt64 subtraction is expressed
using its wrapping addition and multiplication, the operations supported by Clean's witness IR. -/
def stateSlot (message : Var Channels.StateMsg (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  let originHigh : Witgen.FExpr (ZMod p) := .hintGet "sp1.state.origin" 2 0 0
  let originLow : Witgen.FExpr (ZMod p) := .hintGet "sp1.state.origin" 2 0 1
  let origin := originHigh.val * (2 ^ 24 : ℕ) + originLow.val
  let clock := message.clk_high.val * (2 ^ 24 : ℕ) + message.clk_low.val
  (clock + origin * (.const (UInt64.ofNat (UInt64.size - 1)))) / 8

/-- Read the complete typed input prefix from the private hint inventory. -/
def stateInput (name : String) (message : Var Channels.StateMsg (ZMod p)) :
    Input (Witgen.FExpr (ZMod p)) :=
  fromElements (Vector.ofFn fun column : Fin (size Input) =>
    .hintGet name (size Input) (stateSlot message) column)

/-- Unit-demand generation shared by instruction circuits that carry a native CPU state. -/
def stateDemand (name : String)
    (state : Input (Witgen.FExpr (ZMod p)) → Circuits.Types.CPUState (Witgen.FExpr (ZMod p)))
    (activity : Input (Witgen.FExpr (ZMod p)) → Witgen.FExpr (ZMod p))
    (padding : Input (ZMod p) := 0) : Generation (ZMod p) Input :=
  .demand {
    channel := Channels.stateChannel
    trigger := .push
    guard message :=
      let input := stateInput name message
      let current := state input
      .and (activity input =? 1)
        (.and (current.clk_high =? message.clk_high)
          (.and (current.clk_0_16 + current.clk_16_24 * 65536 =? message.clk_low)
            (.and (current.pc[0] =? message.pc0)
              (.and (current.pc[1] =? message.pc1) (current.pc[2] =? message.pc2)))))
    input message := pure (fromElements ((toElements (stateInput (Input := Input) name message)).map
      Cell.witness))
    padding
  }

end SP1Clean.Native.Witgen
