import SP1Clean.Native.Witgen.StateDemand
import SP1Clean.Model.SP1Field
import Clean.Air.WitnessGeneration
import Clean.Utils.Tactics

/-! Executable routing checks for the instruction hint ABI. The fixture crosses a low-clock
rollover, starts at a nonzero origin, preserves repeated requests, and rejects mismatched hints. -/

namespace SP1CleanTest.Core.StateDemand

open Circuit Air.Flat SP1Clean

abbrev Fp := ZMod SP1Prime

structure Inputs (F : Type) where
  enabled : F
  state : Circuits.Types.CPUState F
  next : Channels.StateMsg F
deriving ProvableStruct

def step : GeneralFormalCircuit Fp Inputs unit where
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    Channels.stateChannel.pullIf input.enabled
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
        input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩
    Channels.stateChannel.pushIf input.enabled input.next
  Spec _ _ _ := True
  channelsWithRequirements := [Channels.stateChannel.toRaw]
  ProverAssumptions input _ _ := IsBool input.enabled
  soundness := by
    circuit_proof_start [Channels.stateChannel]
    simpa only [mul_eq_zero, sub_eq_zero] using h_holds
  completeness := by
    circuit_proof_start [Channels.stateChannel]
    change IsBool input_enabled at h_assumptions
    simpa only [IsBool, mul_eq_zero, sub_eq_zero] using h_assumptions

def component (name : String) : Component Fp where
  circuit := { step with name }
  generation := Native.Witgen.stateDemand name (fun input : Inputs (Witgen.FExpr Fp) => input.state)
    (fun input => input.enabled)

def initial : Channels.StateMsg Fp := ⟨1, 2 ^ 24 - 7, 8, 0, 0⟩
def middle : Channels.StateMsg Fp := ⟨2, 1, 12, 0, 0⟩
def finalState : Channels.StateMsg Fp := ⟨2, 265, 16, 0, 0⟩

def requests : Verifier.Program Fp unit where
  main _ := do
    Verifier.push Channels.stateChannel (ProvableType.const initial)
    Verifier.push Channels.stateChannel (ProvableType.const initial)
    Verifier.pull Channels.stateChannel (ProvableType.const finalState)
    Verifier.pull Channels.stateChannel (ProvableType.const finalState)
  Spec _ _ := True
  soundness := by intro _ _; trivial

def ensemble : Ensemble Fp unit where
  tables := [component "first", component "second", component "unused"]
  unique_names := by simp [component]
  channels := [Channels.stateChannel.toRaw]
  unique_channel_names := by simp
  verifier := requests
  tables_channels := by
    intro table member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals
      change [Channels.stateChannel.toRaw] ++ [Channels.stateChannel.toRaw] ⊆ _
      simp
  verifier_channels := by simp [requests, circuit_norm]
  ProverInput := fields (2 + 3 * size Inputs)
  hintTables := [
    { key := "sp1.state.origin", width := 2, offset := 0, rows := 1 },
    { key := "first", width := size Inputs, offset := 2, rows := 1 },
    { key := "second", width := size Inputs, offset := 2 + size Inputs, rows := 2 }]

def first : Inputs Fp := ⟨1, ⟨1, 255, 65529, #v[8, 0, 0]⟩, middle⟩
def second : Inputs Fp := ⟨1, ⟨2, 0, 1, #v[12, 0, 0]⟩, finalState⟩

def input (origin : Vector Fp 2) (secondRow : Inputs Fp) : ensemble.ProverInput Fp :=
  origin ++ toElements first ++ toElements (0 : Inputs Fp) ++ toElements secondRow

def generate (origin : Vector Fp 2) (secondRow : Inputs Fp) : Except String (List Nat) :=
  match WitnessGeneration.generate ensemble 32 () (input origin secondRow) with
  | .error error => .error (toString error)
  | .ok witness => do
    unless WitnessGeneration.constraintsHold witness && WitnessGeneration.channelsBalanced witness do
      throw "generated witness failed constraints or channel balance"
    pure (witness.tables.map fun table => table.table.length)

example : generate #v[1, 2 ^ 24 - 7] second = .ok [2, 2, 0] := by native_decide
example : (generate #v[1, 2 ^ 24 - 7] { second with enabled := 0 }).isOk = false := by native_decide
example : (generate #v[1, 2 ^ 24 - 7]
    { second with state := { second.state with pc := #v[13, 0, 0] } }).isOk = false := by native_decide
example : (generate #v[0, 0] second).isOk = false := by native_decide

end SP1CleanTest.Core.StateDemand
