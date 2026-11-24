import SP1Clean.FormalModel.Contracts.WritePlacement
import SP1Clean.Native.Operations.AddressSum
import SP1Clean.Native.Operations.WriteStreamSource
import Clean.Gadgets.IsZeroField

/-! # Joining one observed guest WRITE byte to its assigned stream position

The cursor advances both absolute guest address and output position by one without field wrap.
All routes consume the actual guest byte. Output and hook requests look up that same byte in
the verifier-fixed stream. A direct hint authorizes it for a fresh node; ignored writes simply
consume it. The receipt identity includes the complete incoming ECALL clock.
-/

namespace SP1Clean.WriteEffects
open Circuit Semantics

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Address the fixed output or hook-request byte at the incoming stream position. -/
def ByteStep.record {F : Type} [Zero F] [One F] (r : ByteStep F) : Record F :=
  ⟨r.previous.sink, 1, r.previous.owner, #v[0,0,0], r.previous.position, #v[r.value,0,0]⟩

/-- Consume a guest byte, advance the cursor and check its route-specific destination. -/
def byteStepMain (r : Var ByteStep (ZMod p)) : Circuit (ZMod p) Unit := do
  positionChannel.pull r.previous
  byteChannel.pull r.read
  assertion AddressSum.circuit ⟨r.previous.address, #v[1,0,0], r.nextAddress⟩
  assertion AddressSum.circuit ⟨r.previous.position, #v[1,0,0], r.nextPosition⟩
  let ignored ← Gadgets.IsZeroField.circuit r.previous.sink
  let direct ← Gadgets.IsZeroField.circuit (r.previous.sink - 14)
  assertZero (r.ignored - ignored)
  assertZero (r.direct - direct)
  recordChannel.pullIf (1 - r.ignored - r.direct) r.record
  nodeByteChannel.pushIf r.direct r.nodeByte
  positionChannel.push r.next

instance byteStepElaborated : ElaboratedCircuit (ZMod p) ByteStep unit byteStepMain := by elaborate_circuit

/-- The two bounded positions advance once and the route flags match the sink. -/
def ByteStep.Valid (r : ByteStep (ZMod p)) : Prop :=
  Address.Bounded r.previous.address ∧ Address.Bounded r.previous.position ∧
  Address.Bounded r.nextAddress ∧ Address.Bounded r.nextPosition ∧
  Address.toNat r.nextAddress = Address.toNat r.previous.address + 1 ∧
  Address.toNat r.nextPosition = Address.toNat r.previous.position + 1 ∧
  r.ignored = (if r.previous.sink = 0 then 1 else 0) ∧ r.direct = (if r.previous.sink = 14 then 1 else 0)

omit [Fact (2^17 < p)] in
private theorem unitAddress : Address.Bounded (#v[1,0,0] : fields 3 (ZMod p)) ∧
    Address.toNat (#v[1,0,0] : fields 3 (ZMod p)) = 1 := by
  constructor
  · intro i; fin_cases i <;> simp [ZMod.val_one]
  · simp [Address.toNat, ZMod.val_one]

/-- Checked transition for a single destination position. -/
def byteStepCircuit : GeneralFormalCircuit (ZMod p) ByteStep unit where
  name := "sp1.native.write_position"
  main := byteStepMain
  elaborated := byteStepElaborated
  computableWitnesses := by computable_witnesses [ByteStep.read, ByteStep.record, ByteStep.nodeByte, ByteStep.next]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  channelsWithRequirements := [recordChannel.toRaw, nodeByteChannel.toRaw, positionChannel.toRaw]
  soundness := by
    circuit_proof_start [byteStepMain, AddressSum.circuit, AddressSum.Spec, Gadgets.IsZeroField.circuit,
      positionChannel, byteChannel, recordChannel, nodeByteChannel]
    simp only [sub_eq_zero] at h_holds
    obtain ⟨⟨prevAddr, _, nextAddr, addr⟩, ⟨prevPos, _, nextPos, pos⟩, ignored, direct, sameI, sameD⟩ := h_holds
    refine ⟨⟨prevAddr, prevPos, nextAddr, nextPos, (unitAddress (p := p)).2 ▸ addr, (unitAddress (p := p)).2 ▸ pos,
      sameI.trans ignored, sameD.trans direct⟩, ?_⟩
    rw [sameI, sameD, ignored, direct]
    have neq : (0 : ZMod p) ≠ 14 := by intro h; have := congrArg ZMod.val h; simp at this
    by_cases i : input_previous_sink = 0
    · subst input_previous_sink
      simp [neq]
    · by_cases d : input_previous_sink = 14 <;> simp [i, d, Ne.symm neq]
  completeness := by
    circuit_proof_start [byteStepMain, AddressSum.circuit, AddressSum.Spec, Gadgets.IsZeroField.circuit,
      positionChannel, byteChannel, recordChannel, nodeByteChannel]
    obtain ⟨prevAddr, prevPos, nextAddr, nextPos, addr, pos, ignored, direct⟩ := h_assumptions
    simp only [sub_eq_zero] at h_env ⊢
    exact ⟨⟨prevAddr, (unitAddress (p := p)).1, nextAddr, (unitAddress (p := p)).2.symm ▸ addr⟩,
      ⟨prevPos, (unitAddress (p := p)).1, nextPos, (unitAddress (p := p)).2.symm ▸ pos⟩, ignored.trans h_env.1.symm, direct.trans h_env.2.symm⟩

/-- Both successor columns are determined by the incoming packet cursor. -/
def ByteStep.populate (previous : Placement (ZMod p)) (byte : ZMod p) : ByteStep (ZMod p) :=
  ⟨previous, Address.ofNat (Address.toNat previous.address + 1), Address.ofNat (Address.toNat previous.position + 1), byte, if previous.sink = 0 then 1 else 0, if previous.sink = 14 then 1 else 0⟩

theorem ByteStep.populate_valid (previous : Placement (ZMod p)) (byte : ZMod p)
    (address : Address.Bounded previous.address) (position : Address.Bounded previous.position)
    (a : Address.toNat previous.address + 1 < 2^48) (i : Address.toNat previous.position + 1 < 2^48) :
    (ByteStep.populate previous byte).Valid :=
  ⟨address, position, Address.bounded_ofNat _, Address.bounded_ofNat _, Address.toNat_ofNat _ a, Address.toNat_ofNat _ i, rfl, rfl⟩

end SP1Clean.WriteEffects
