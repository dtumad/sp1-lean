import SP1Clean.Native.Operations.HostHintQueueTerminal
import ToClean.Air.TableBuild

/-! # Constructing the physical outgoing hint cursor -/

namespace SP1Clean.HostHintQueueTerminal

open Circuit Air.Flat HostHintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Materialize the last semantic hint access as two canonical timestamp limbs. -/
def inputFor (clock : BitVec 48) : Inputs (ZMod p) :=
  ⟨1, 1, (clock.toNat / 2 ^ 24 : ℕ), (clock.toNat % 2 ^ 24 : ℕ)⟩

private theorem input_valid (clock : BitVec 48) : Valid (inputFor (p := p) clock) := by
  have bounded := clock.isLt
  have field := Fact.out (p := 2 ^ 25 < p)
  have high : clock.toNat / 2 ^ 24 < 2 ^ 24 := by omega
  have low := Nat.mod_lt clock.toNat (by decide : 0 < 2 ^ 24)
  exact ⟨rfl, rfl, by simpa only [inputFor, ZMod.val_natCast_of_lt (show clock.toNat / 2^24 < p by omega)] using high,
    by simpa only [inputFor, ZMod.val_natCast_of_lt (show clock.toNat % 2^24 < p by omega)] using low⟩

private theorem fixed_input (target : State (ZMod p)) (clock : BitVec 48)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (component target).FixedRowsMatch ([inputFor clock].map ((component target).buildRow · data hint)) := by
  refine ⟨rfl, ?_⟩
  intro index bound
  change index < 1 at bound
  have zero : index = 0 := by omega
  subst index
  have same : fromElements (M := (component target).Input)
      (rowPrefix (size (component target).Input) ((component target).buildRow (inputFor clock) data hint)) = inputFor clock := by
    exact (congrArg (fromElements (M := (component target).Input))
      ((component target).rowPrefix_buildRow (inputFor clock) data hint)).trans (ProvableType.fromElements_toElements _)
  erw [same]
  simp only [WitnessGeneration.PreallocatedMode.FixedAt, inputFor, circuit_norm]
  erw [ProvableStruct.toList_toElements (α := Inputs), ProvableStruct.toList_toElements (α := Inputs)]
  simp only [circuit_norm]
  repeat' constructor

/-- The official row builder constructs the single verifier-fixed table for every private clock. -/
def tableFor (target : State (ZMod p)) (clock : BitVec 48) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let c := component target
  let rows := [inputFor clock]
  let own := c.inputData rows data
  Table.build c rows own (.empty _) (by change 1 ≤ UInt64.size; decide) (fixed_input target clock own _) (c.inputData_consistent rows data)

/-- The physical compiler table satisfies Clean's row constraints and its channel guarantees. -/
theorem tableFor_valid (target : State (ZMod p)) (clock : BitVec 48) (data : ProverData (ZMod p)) :
    (tableFor target clock data).Constraints ∧ (tableFor target clock data).Guarantees := by
  have honest (input) (member : input ∈ [inputFor (p := p) clock]) : Valid input := List.mem_singleton.mp member ▸ input_valid clock
  unfold tableFor
  constructor
  · apply Table.build_constraints
    exact honest
  · apply Table.build_guarantees
    exact honest

/-- The generated table has exactly the private pull and public push, even when they have the same key. -/
theorem tableFor_ledger (publicClock head allocated : ℕ) (clock : BitVec 48) (data : ProverData (ZMod p)) :
    let target := State.encode (p := p) publicClock head allocated
    (tableFor target clock data).interactionsWith stateChannel.toRaw =
      [stateChannel.pulledValue (State.encode clock.toNat head allocated), stateChannel.pushedValue target] := by
  dsimp only
  let target := State.encode (p := p) publicClock head allocated
  let c := component target
  let own := c.inputData [inputFor clock] data
  let row := c.buildRow (inputFor clock) own (.empty _)
  let env := Environment.fromArray row own
  have cells := c.rowInput_buildRow (inputFor clock) own own (.empty _)
  change valueFromOffset Inputs 0 env = inputFor clock at cells
  rw [Table.interactionsWith]
  change ([row].flatMap fun r => (c.operations.interactionsWith stateChannel.toRaw).map
    (AbstractInteraction.eval (Environment.fromArray r own))) = _
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, Component.interactionsWith_eq]
  change ((main target (varFromOffset Inputs 0)).operations (size Inputs)).interactionValuesWith stateChannel.toRaw env = _
  rw [values, eval_varFromOffset_valueFromOffset, cells]
  rfl

end SP1Clean.HostHintQueueTerminal
