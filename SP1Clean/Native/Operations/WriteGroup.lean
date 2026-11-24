import SP1Clean.Native.Operations.WriteGroupCoordinates
import SP1Clean.Native.Operations.WriteGroupBytes
import SP1Clean.Native.Operations.WriteBlockSource
import Clean.Gadgets.IsZeroField

/-! # A complete, clock-bound WRITE word placement

The row consumes one original octet and its verified finite window. Nonempty intervals link
the packet's previous and next byte positions. Data-carrying routes consume one fixed or
allocated block and consume the next block exactly when the interval crosses its boundary.
Ignored output and empty intervals still consume their actual guest word.
-/

namespace SP1Clean.WriteEffects
open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

omit [Fact p.Prime] in
private theorem fourFits : 2^4 < p := by have h : 2^17 < p := Fact.out; omega

/-- Enable the first destination block for a nonempty, retained interval. -/
def Group.leftGate {F : Type} [One F] [Sub F] [Mul F] (r : Group F) : F := (1-r.ignored)*r.plan.nonempty
/-- Enable the second destination block when retained bytes cross the block boundary. -/
def Group.rightGate {F : Type} [One F] [Sub F] [Mul F] (r : Group F) : F := (1-r.ignored)*r.plan.second

/-- Check the byte placement and exchange the selected blocks and cursor messages. -/
def groupMain (r : Var Group (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← groupCoordinatesCircuit r
  assertion groupBytesCircuit r
  let ignore ← Gadgets.IsZeroField.circuit r.previous.sink
  assertZero (r.ignored - ignore)
  assertBool r.plan.nonempty
  assertBool r.plan.second
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) r.leftSize
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) r.rightSize
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) r.plan.firstExtent
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) r.plan.secondExtent
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) (r.leftGate * (r.leftSize-r.plan.firstExtent))
  assertion (Gadgets.ToBits.rangeCheck 4 fourFits) (r.rightGate * (r.rightSize-r.plan.secondExtent))
  octetsChannel.pull r.octets
  sliceChannel.pull r.plan
  positionChannel.pullIf r.plan.nonempty r.previous
  blockChannel.pullIf r.leftGate (r.block false)
  blockChannel.pullIf r.rightGate (r.block true)
  positionChannel.pushIf r.plan.nonempty r.next

instance groupElaborated : ElaboratedCircuit (ZMod p) Group unit groupMain := by elaborate_circuit

/-- Both selected destination intervals fall within the occupied parts of their blocks. -/
def Group.Extents (r : Group (ZMod p)) : Prop :=
  r.leftSize.val < 16 ∧ r.rightSize.val < 16 ∧ r.plan.firstExtent.val < 16 ∧ r.plan.secondExtent.val < 16 ∧
    (r.leftGate = 1 → r.plan.firstExtent.val ≤ r.leftSize.val) ∧
    (r.rightGate = 1 → r.plan.secondExtent.val ≤ r.rightSize.val)

/-- The group respects its coordinates, destination bytes, route and occupied extents. -/
def Group.Valid (r : Group (ZMod p)) : Prop :=
  r.Coordinates ∧ r.BytesMatch ∧ r.ignored = (if r.previous.sink = 0 then 1 else 0) ∧
    IsBool r.plan.nonempty ∧ IsBool r.plan.second ∧ r.Extents

omit [Fact (2^17 < p)] in
private theorem enabled_bool {value flag : ZMod p} (flagBit : IsBool flag) :
    IsBool ((1-(if value = 0 then 1 else 0 : ZMod p))*flag) := by
  by_cases h : value = 0
  · simp [h,IsBool]
  · simpa [h] using flagBit

private theorem extent_iff (gate lower upper : ZMod p) (bit : IsBool gate)
    (lo : lower.val < 16) (hi : upper.val < 16) :
    (gate*(upper-lower)).val < 16 ↔ (gate = 1 → lower.val ≤ upper.val) := by
  rcases bit with rfl | rfl
  · simp
  · simp only [one_mul, true_implies]
    constructor
    · intro diff
      have hp : 2^17 < p := Fact.out
      have same : lower+(upper-lower) = upper := by ring
      have natural := congrArg ZMod.val same
      rw [ZMod.val_add_of_lt (by omega)] at natural
      omega
    · intro bound
      rw [ZMod.val_sub bound]
      omega

private theorem group_sound (r : Group (ZMod p)) (coordinates : r.Coordinates) (content : r.BytesMatch)
    (ignore : r.ignored = (if r.previous.sink = 0 then 1 else 0))
    (active : IsBool r.plan.nonempty) (crossing : IsBool r.plan.second)
    (left : r.leftSize.val < 16) (right : r.rightSize.val < 16)
    (first : r.plan.firstExtent.val < 16) (last : r.plan.secondExtent.val < 16)
    (a : (r.leftGate*(r.leftSize-r.plan.firstExtent)).val < 16) (b : (r.rightGate*(r.rightSize-r.plan.secondExtent)).val < 16) :
    r.Valid ∧ IsBool r.leftGate ∧ IsBool r.rightGate := by
  have la : IsBool r.leftGate := by simpa only [Group.leftGate,ignore] using enabled_bool (value := r.previous.sink) active
  have rb : IsBool r.rightGate := by simpa only [Group.rightGate,ignore] using enabled_bool (value := r.previous.sink) crossing
  exact ⟨⟨coordinates,content,ignore,active,crossing,left,right,first,last,(extent_iff _ _ _ la first left).mp a,
    (extent_iff _ _ _ rb last right).mp b⟩,la,rb⟩

/-- Formal circuit for placing one observed guest word into its destination stream. -/
def groupCircuit : GeneralFormalCircuit (ZMod p) Group unit where
  name := "sp1.native.write_word_placement"
  main := groupMain
  elaborated := groupElaborated
  computableWitnesses := by computable_witnesses [Group.leftGate, Group.rightGate]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid ∧ r.HonestCoordinates
  channelsWithRequirements := [blockChannel.toRaw, positionChannel.toRaw]
  soundness := by
    circuit_proof_start [groupMain,groupCoordinatesCircuit,groupBytesCircuit,Gadgets.IsZeroField.circuit,Gadgets.ToBits.rangeCheck,
      octetsChannel,sliceChannel,positionChannel,blockChannel,Group.leftGate,Group.rightGate]
    obtain ⟨coords,bytes,zero,same,active,cross,left,right,first,last,a,b⟩ := h_holds
    have checked := group_sound _ coords bytes ((sub_eq_zero.mp same).trans zero) active cross left right first last a b
    exact ⟨checked.1, active, checked.2.1,checked.2.2⟩
  completeness := by
    circuit_proof_start [groupMain,groupCoordinatesCircuit,groupBytesCircuit,Gadgets.IsZeroField.circuit,Gadgets.ToBits.rangeCheck,
      octetsChannel,sliceChannel,positionChannel,blockChannel,Group.leftGate,Group.rightGate]
    obtain ⟨⟨_,content,ignore,active,cross,left,right,first,last,a,b⟩,coords⟩ := h_assumptions
    have la := enabled_bool (value := input_previous_sink) active
    have rb := enabled_bool (value := input_previous_sink) cross
    rw [← ignore] at la rb
    exact ⟨coords,content,sub_eq_zero.mpr (ignore.trans h_env.2.symm),active,cross,left,right,first,last,
      (extent_iff _ _ _ la first left).mpr a,(extent_iff _ _ _ rb last right).mpr b⟩

end SP1Clean.WriteEffects
