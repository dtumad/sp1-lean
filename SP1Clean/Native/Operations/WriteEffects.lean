import SP1Clean.FormalModel.Contracts.WriteEffects
import SP1Clean.FormalModel.Contracts.WriteBuffer
import SP1Clean.Native.Operations.WriteDescriptor
import SP1Clean.Circuits.Gadgets.U16toU8Safe
import SP1Clean.Semantics.Specs.U16toU8Bytes

/-! # Header and word receipts for released WRITE effects

Each header emits one classified effect request, including zero-length writes. Each received word
emits all eight bounded bytes in address order, independent of descriptor and length.
-/

namespace SP1Clean.WriteEffects
open Circuit Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Classification is deterministic on the complete descriptor of the incoming packet. -/
def Request.Valid (r : Request (ZMod p)) : Prop :=
  r.header.descriptor.isU64 ∧ r.route = ((WriteRoute.ofDescriptor r.header.descriptor.toBitVec64).tag : ZMod p)

/-- The row compiler reads the original packet, including the exact observed x12 length. -/
def Request.populate (h : WritePacket.Header (ZMod p)) : Request (ZMod p) :=
  ⟨h, (WriteRoute.ofDescriptor h.descriptor.toBitVec64).tag⟩

omit [Fact (2 ^ 17 < p)] in
theorem Request.populate_valid (h : WritePacket.Header (ZMod p)) (bound : h.descriptor.isU64) :
    (Request.populate h).Valid := ⟨bound, rfl⟩

def requestMain (r : Var Request (ZMod p)) : Circuit (ZMod p) Unit := do
  let route ← WriteDescriptor.circuit r.header.descriptor
  assertZero (r.route - route)
  WriteBuffer.effectHeaderChannel.pull r.header
  requestChannel.push r

instance requestElaborated : ElaboratedCircuit (ZMod p) Request unit requestMain := by elaborate_circuit

/-- One checked route and its original clock, address, length and descriptor. -/
def requestCircuit : GeneralFormalCircuit (ZMod p) Request unit where
  name := "sp1.native.write_route"
  main := requestMain
  elaborated := requestElaborated
  computableWitnesses := by computable_witnesses
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  channelsWithRequirements := [requestChannel.toRaw]
  soundness := by
    circuit_proof_start [requestMain, WriteDescriptor.circuit, WriteBuffer.effectHeaderChannel, requestChannel]
    obtain ⟨⟨bounded, tag⟩, same⟩ := h_holds
    exact ⟨bounded, (sub_eq_zero.mp same).trans tag⟩
  completeness := by
    circuit_proof_start [requestMain, WriteDescriptor.circuit, WriteBuffer.effectHeaderChannel, requestChannel]
    exact ⟨h_assumptions.1, sub_eq_zero.mpr (h_assumptions.2.trans (h_env h_assumptions.1).2.symm)⟩

/-- The bus payload shares the raw word's exact clock and absolute aligned key. -/
def WordRow.octets {F : Type} [Sub F] [Mul F] (inverse : F) (r : WordRow F) : Octets F :=
  ⟨r.read.key, r.read.clock, U16toU8OperationSafe.bytes inverse r.read.value r.low⟩

def WordRow.populate (read : WriteProbe.Read (ZMod p)) : WordRow (ZMod p) :=
  ⟨read, (U16toU8OperationSafe.populate read.value).low_bytes⟩

/-- The emitted bytes are exactly the eight extracted lanes, including both partial endpoints. -/
def WordRow.Valid (r : WordRow (ZMod p)) : Prop :=
  ∀ i : Fin 8, (r.octets (256 : ZMod p)⁻¹).bytes[i].val < 256 ∧
    BitVec.ofNat 8 (r.octets (256 : ZMod p)⁻¹).bytes[i].val = r.read.value.toBitVec64.extractLsb' (8 * i.val) 8

theorem WordRow.valid_of_decomp (r : WordRow (ZMod p))
    (split : U16toU8OperationSafe.DecompSpec r.read.value ⟨r.low⟩) : r.Valid := by
  obtain ⟨bound, word⟩ := split.bytes
  intro i
  refine ⟨bound i, ?_⟩
  rw [word, Word.bytesValue_extract]
  simp only [Fin.getElem_fin, Vector.getElem_map]
  rfl

def wordMain (r : Var WordRow (ZMod p)) : Circuit (ZMod p) Unit := do
  WriteBuffer.wordChannel.pull r.read
  assertion U16toU8OperationSafe.circuit ⟨r.read.value, ⟨r.low⟩, 1⟩
  octetsChannel.push (r.octets (.const (256 : ZMod p)⁻¹))

instance wordElaborated : ElaboratedCircuit (ZMod p) WordRow unit wordMain := by elaborate_circuit

/-- Reuses the ordinary safe SP1 byte decoder for every physical word sampled by WRITE. -/
def wordCircuit : GeneralFormalCircuit (ZMod p) WordRow unit where
  name := "sp1.native.write_octets"
  main := wordMain
  elaborated := wordElaborated
  computableWitnesses := by computable_witnesses [WordRow.octets, U16toU8OperationSafe.bytes]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.read.value.isU64 ∧ r.low = (U16toU8OperationSafe.populate r.read.value).low_bytes
  channelsWithRequirements := [octetsChannel.toRaw]
  soundness := by
    circuit_proof_start [wordMain, U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions,
      WriteBuffer.wordChannel, octetsChannel]
    exact WordRow.valid_of_decomp _ (h_holds rfl)
  completeness := by
    circuit_proof_start [wordMain, U16toU8OperationSafe.circuit, U16toU8OperationSafe.Assumptions,
      WriteBuffer.wordChannel, octetsChannel]
    obtain ⟨bound, low⟩ := h_assumptions
    rw [low]
    exact U16toU8OperationSafe.spec_populate (bound 0) (bound 1) (bound 2) (bound 3) 1

theorem WordRow.populate_honest (read : WriteProbe.Read (ZMod p)) (bound : read.value.isU64)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    wordCircuit.ProverAssumptions (WordRow.populate read) data hint := ⟨bound, rfl⟩

end SP1Clean.WriteEffects
