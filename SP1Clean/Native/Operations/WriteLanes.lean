import SP1Clean.FormalModel.Contracts.WritePlacement
import SP1Clean.Proofs.Operations.WriteEffects
import Clean.Gadgets.Boolean

/-! # Position-keyed bytes from complete authenticated WRITE octets

A word always consumes one full octets receipt. Its eight potential emissions remain in the
ledger, including unselected lanes of boundary words. The consumer's contiguous packet walk
determines the actual selection.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime]

def laneMain (r : Var LaneRow (ZMod p)) : Circuit (ZMod p) Unit := do
  octetsChannel.pull r.octets
  forEach (Vector.ofFn fun i : Fin 8 => i) fun i => do
    assertBool r.selected[i]
    byteChannel.pushIf r.selected[i] (r.lane i (.const i.val))

instance laneElaborated : ElaboratedCircuit (ZMod p) LaneRow unit laneMain := by elaborate_circuit

/-- All eight flags are constrained independently, including when the enclosing descriptor is ignored. -/
def laneCircuit : GeneralFormalCircuit (ZMod p) LaneRow unit where
  name := "sp1.native.write_byte_lanes"
  main := laneMain
  elaborated := laneElaborated
  computableWitnesses := by computable_witnesses [LaneRow.lane, Address.offset]
  Spec r _ _ := ∀ i : Fin 8, IsBool r.selected[i]
  ProverAssumptions r _ _ := ∀ i : Fin 8, IsBool r.selected[i]
  channelsWithRequirements := [byteChannel.toRaw]
  soundness := by
    circuit_proof_start [laneMain, octetsChannel, byteChannel, LaneRow.lane]
    exact h_holds
  completeness := by
    circuit_proof_start [laneMain, octetsChannel, byteChannel, LaneRow.lane]
    exact h_assumptions

/-- Honest selection follows just the original half-open interval and the absolute word key. -/
def LaneRow.populate (r : Octets (ZMod p)) (start length : Nat) : LaneRow (ZMod p) :=
  ⟨r, Vector.ofFn fun i => if start ≤ Address.toNat r.key + i.val ∧ Address.toNat r.key + i.val < start + length then 1 else 0⟩

theorem LaneRow.populate_honest (r : Octets (ZMod p)) (start length : Nat) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    laneCircuit.ProverAssumptions (LaneRow.populate r start length) data hint := by
  intro i
  simp only [populate, Fin.getElem_fin, Vector.getElem_ofFn]
  split <;> simp [IsBool]

end SP1Clean.WriteEffects
