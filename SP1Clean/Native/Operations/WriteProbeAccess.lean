import SP1Clean.FormalModel.Contracts.WriteReadback
import SP1Clean.Circuits.Channels.Channels
import ToClean.Circuit.ReceiptList

/-! # WRITE versions from the predecessor records of real accesses

A pull supplies its actual predecessor word from the previous Memory timestamp through the
accessing instruction's incoming CPU clock. A later aliased pull in the same instruction may
have an empty interval. The probe requires a representable clock in both bounds.
-/

namespace SP1Clean.WriteProbe.AccessSupply

open Circuit Air.Flat Channels

/-- Attach the original address, predecessor time and word to the accessing row's released bus clock. -/
def atClock {F : Type} (time : F × F) (prior : MemoryMsg F) : Readback F :=
  ⟨#v[prior.addr0, prior.addr1, prior.addr2], prior.clk_high, prior.clk_low, time.1, time.2, prior.value⟩

/-- Instruction predecessors use the original incoming State clock. -/
def readback {F : Type} (incoming : StateMsg F) (prior : MemoryMsg F) : Readback F :=
  atClock (incoming.clk_high, incoming.clk_low) prior

variable {p : ℕ} [Fact p.Prime] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

theorem eval_atClock (env : Environment (ZMod p)) (time : Expression (ZMod p) × Expression (ZMod p))
    (prior : Var MemoryMsg (ZMod p)) : eval env (atClock time prior) =
      atClock (env time.1, env time.2) (eval env prior) := by
  cases time
  cases prior
  simp only [atClock, circuit_norm]

/-- A positive private source comes from an actual positive original Memory pull in the same
physical row, with its upper bound fixed by that row's own clock. -/
def FromPredecessor (table : Table (ZMod p)) (upper : Environment (ZMod p) → ZMod p × ZMod p)
    (record : Readback (ZMod p)) : Prop :=
  ∃ physical ∈ table.table,
    let env := table.environment physical
    ∃ (gate : ZMod p) (prior : MemoryMsg (ZMod p)), gate ≠ 0 ∧
      memoryChannel.pulledIfValue gate prior ∈ table.component.operations.interactionValuesWith memoryChannel.toRaw env ∧
      record = atClock (upper env) prior

theorem eval_readback (env : Environment (ZMod p)) (incoming : Var StateMsg (ZMod p))
    (prior : Var MemoryMsg (ZMod p)) : eval env (readback incoming prior) = readback (eval env incoming) (eval env prior) := by
  cases incoming
  cases prior
  simp only [readback, atClock, circuit_norm]

/-- Existing symbolic Memory emissions and the incoming State of their physical row. -/
structure Layout (p : ℕ) [Fact p.Prime] (Input : TypeMap) [ProvableType Input] where
  /-- Typed original Memory emissions at the supplied symbolic row offset. -/
  memory : Var Input (ZMod p) → ℕ → List (ChannelInteraction (memoryChannel (p := p)))
  /-- Incoming CPU State at the same physical row. -/
  incoming : Var Input (ZMod p) → StateMsg (Expression (ZMod p))

namespace Layout

/-- All physical predecessors, including disabled and repeated pulls. -/
def pulls (layout : Layout p Input) (input : Var Input (ZMod p)) (offset : ℕ) :=
  (layout.memory input offset).filter fun i => i.direction == .pull

/-- Count actual pulls in the canonical row layout. -/
def count (layout : Layout p Input) : ℕ := (layout.pulls (varFromOffset Input 0) (size Input)).length

/-- Each symbolic instantiation exposes the same physical pull positions. -/
def FixedShape (layout : Layout p Input) : Prop :=
  ∀ input offset, (layout.pulls input offset).length = layout.count

private def atIndex (layout : Layout p Input) (fixed : layout.FixedShape) (i : Fin layout.count)
    (input : Var Input (ZMod p)) (offset : ℕ) : ChannelInteraction (memoryChannel (p := p)) :=
  (layout.pulls input offset)[i.val]'(by rw [fixed]; exact i.isLt)

/-- Original Memory multiplicity gates each private receipt, independently of sibling accesses. -/
def projections (layout : Layout p Input) (fixed : layout.FixedShape) :
    List (Receipt.Projection (ZMod p) Input Readback) :=
  List.ofFn fun i : Fin layout.count =>
    ⟨fun input offset => (layout.atIndex fixed i input offset).mult,
      fun input offset => readback (layout.incoming input) (layout.atIndex fixed i input offset).msg⟩

theorem projected (layout : Layout p Input) (fixed : layout.FixedShape)
    (input : Var Input (ZMod p)) (offset : ℕ) :
    (layout.projections fixed).map (fun pr =>
      (readbackChannel.pushedIf (pr.gate input offset) (pr.message input offset)).toRaw) =
    (layout.pulls input offset).map (fun i =>
      (readbackChannel.pushedIf i.mult (readback (layout.incoming input) i.msg)).toRaw) := by
  apply List.ext_getElem
  · simp only [projections, List.length_map, List.length_ofFn]
    exact (fixed input offset).symm
  · intro i left right
    simp only [projections, List.getElem_map, List.getElem_ofFn, atIndex]

/-- Add the private predecessor observations without changing the original component's layout. -/
def circuit (layout : Layout p Input) (fixed : layout.FixedShape)
    (provider : GeneralFormalCircuit (ZMod p) Input Output) : GeneralFormalCircuit (ZMod p) Input Output :=
  Receipt.many provider readbackChannel (fun _ _ => trivial) (layout.projections fixed)

theorem added (layout : Layout p Input) (fixed : layout.FixedShape)
    (provider : GeneralFormalCircuit (ZMod p) Input Output) (input : Var Input (ZMod p)) (offset : ℕ) :
    ((((layout.circuit fixed provider).main input).operations offset).interactionsWith readbackChannel.toRaw) =
      ((provider.main input).operations offset).interactionsWith readbackChannel.toRaw ++
        (layout.pulls input offset).map (fun i =>
          (readbackChannel.pushedIf i.mult (readback (layout.incoming input) i.msg)).toRaw) := by
  exact (Receipt.many_receipts provider readbackChannel (fun _ _ => trivial) (layout.projections fixed) input offset).trans
    (congrArg (_ ++ ·) (layout.projected fixed input offset))

end Layout

end SP1Clean.WriteProbe.AccessSupply
