import SP1Clean.FormalModel.Contracts.WriteGroup
import SP1Clean.Native.Operations.AddressSum
import SP1Clean.Proofs.Operations.AddressDiv8

/-! # Nonwrapping coordinates for one grouped WRITE word

The guest cursor starts one byte before the first selected lane. The output cursor advances by
the selected byte count and is divided into its exact aligned block and initial offset. All these
calculations are locally range-checked and have no shared lookup-channel traffic.
-/

namespace SP1Clean.WriteEffects
open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

def groupCoordinatesMain (r : Var Group (ZMod p)) : Circuit (ZMod p) Unit := do
  r.previous.clock === r.octets.clock
  let out ← AddressDiv8.circuit r.division
  out.quotient === r.firstBlock
  out.remainder === r.plan.offset
  assertion AddressSum.circuit ⟨r.previous.address, #v[1,0,0], Address.offset r.octets.key r.plan.first⟩
  assertion AddressSum.circuit ⟨r.previous.position, #v[r.plan.size,0,0], r.nextPosition⟩
  assertion AddressSum.circuit ⟨r.firstBlock, #v[1,0,0], r.nextBlock⟩

instance groupCoordinatesElaborated : ElaboratedCircuit (ZMod p) Group unit groupCoordinatesMain := by elaborate_circuit

def Group.Coordinates (r : Group (ZMod p)) : Prop :=
  r.previous.clock = r.octets.clock ∧ Address.Bounded r.firstBlock ∧
  Address.toNat r.firstBlock = Address.toNat r.previous.position / 8 ∧ r.plan.offset.val = Address.toNat r.previous.position % 8 ∧
  AddressSum.Spec ⟨r.previous.address, #v[1,0,0], Address.offset r.octets.key r.plan.first⟩ ∧
  AddressSum.Spec ⟨r.previous.position, #v[r.plan.size,0,0], r.nextPosition⟩ ∧
  AddressSum.Spec ⟨r.firstBlock, #v[1,0,0], r.nextBlock⟩

def Group.HonestCoordinates (r : Group (ZMod p)) : Prop := r.Coordinates ∧ r.division = AddressDiv8.populate (Address.asWord r.previous.position)

omit [Fact (2^17 < p)] in
private theorem coordinate_sound (r : Group (ZMod p)) (out : AddressDiv8.Output (ZMod p))
    (clock : r.previous.clock = r.octets.clock) (div : AddressDiv8.Spec r.division out)
    (block : out.quotient = r.firstBlock) (offset : out.remainder = r.plan.offset)
    (first : AddressSum.Spec ⟨r.previous.address, #v[1,0,0], Address.offset r.octets.key r.plan.first⟩)
    (size : AddressSum.Spec ⟨r.previous.position, #v[r.plan.size,0,0], r.nextPosition⟩)
    (next : AddressSum.Spec ⟨r.firstBlock, #v[1,0,0], r.nextBlock⟩) : r.Coordinates := by
  obtain ⟨_,_,bound,q,rem,_⟩ := div
  rw [block] at bound q
  rw [offset] at rem
  exact ⟨clock,bound,by simpa only [Group.division,Address.toNat_asWord] using q,
    by simpa only [Group.division,Address.toNat_asWord] using rem,first,size,next⟩

private theorem div_checks (r : Group (ZMod p)) (honest : r.HonestCoordinates) :
    AddressDiv8.ProverAssumptions r.division ∧ ∀ out : AddressDiv8.Output (ZMod p), AddressDiv8.Spec r.division out →
      out.quotient = r.firstBlock ∧ out.remainder = r.plan.offset := by
  obtain ⟨⟨_,indexBound,index,offset,_,size,_⟩,pop⟩ := honest
  refine ⟨⟨Address.isU64_asWord size.1, by simpa only [Group.division,Address.toNat_asWord] using Address.toNat_lt size.1,pop⟩,?_⟩
  intro out checked
  obtain ⟨_,_,bound,q,rem,_⟩ := checked
  simp only [Group.division,Address.toNat_asWord] at q rem
  constructor
  · rw [← Address.ofNat_toNat bound, ← Address.ofNat_toNat indexBound, q,index]
  · exact ZMod.val_injective p (rem.trans offset.symm)

omit [Fact (2^17 < p)] in
private theorem eval_division (env : Environment (ZMod p)) (r : Var Group (ZMod p)) :
    ProvableStruct.eval env r.division = (ProvableStruct.eval env r).division := by
  cases r
  simp only [Group.division,Address.asWord,circuit_norm]

def groupCoordinatesCircuit : GeneralFormalCircuit (ZMod p) Group unit where
  main := groupCoordinatesMain
  elaborated := groupCoordinatesElaborated
  computableWitnesses := by computable_witnesses [Group.division,Address.asWord,Address.offset]
  Spec r _ _ := r.Coordinates
  ProverAssumptions r _ _ := r.HonestCoordinates
  soundness := by
    circuit_proof_start [groupCoordinatesMain, AddressDiv8.circuit, eval_division, AddressSum.circuit, Address.offset]
    obtain ⟨clock,div,block,remainder,first,size,next⟩ := h_holds
    exact coordinate_sound _ _ clock div block remainder first size next
  completeness := by
    circuit_proof_start [groupCoordinatesMain, AddressDiv8.circuit, eval_division, AddressSum.circuit, Address.offset]
    obtain ⟨a,bind⟩ := div_checks _ h_assumptions
    obtain ⟨valid,_⟩ := h_assumptions
    obtain ⟨q,off⟩ := bind _ (h_env a)
    exact ⟨valid.1,a,q,off,valid.2.2.2.2.1,valid.2.2.2.2.2.1,valid.2.2.2.2.2.2⟩

end SP1Clean.WriteEffects
