import SP1Clean.FormalModel.Contracts.WriteAllocation
import SP1Clean.Native.Operations.ClockOrder
import SP1Clean.Native.Operations.ClockParts
import SP1Clean.Native.Operations.AddressSum
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Operations.HintNodeAllocateLedger

/-! # Checked WRITE ticket receiver and fresh-node step

A call moves between the same clocked states as HINT_LEN and HINT_READ. Private cursor
interactions enforce reverse return order. Fresh nodes use the existing checked allocator
and require their own word witness even when their length is zero.
-/

namespace SP1Clean.WriteAllocation
open Circuit WriteEffects

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)] [Fact (2^24 < p)] [Fact (2^25 < p)]

/-- A ticket and both clock representations identify the same strictly later queue operation. -/
def Open.Valid (r : Open (ZMod p)) : Prop :=
  IsBool r.ticket.direct ∧ r.timestamp.Bounded ∧ r.ticket.clock = r.timestamp.address ∧ ClockOrder.Spec r.order

/-- Open and close an allocation batch on the global persistent queue. -/
def openMain (r : Var Open (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool r.ticket.direct
  assertion ClockParts.circuit r.timestamp
  assertion (Gadgets.Equality.circuit (fields 3)) (r.ticket.clock,r.timestamp.address)
  let _ ← ClockOrder.circuit r.order
  queueEffectChannel.pull r.ticket
  HostHintQueue.stateChannel.pull r.previous
  cursorChannel.push r.first
  cursorChannel.pull r.last
  HostHintQueue.stateChannel.push r.outgoing

instance openElaborated : ElaboratedCircuit (ZMod p) Open unit openMain := by elaborate_circuit

/-- Full circuit contract for chronological direct hints and hook calls, including zero returns. -/
def openCircuit : GeneralFormalCircuit (ZMod p) Open unit where
  name := "sp1.native.hint_allocation_call"
  main := openMain
  elaborated := openElaborated
  computableWitnesses := by computable_witnesses [Open.order, ClockParts.address, ClockParts.high24, ClockParts.low24]
  channelsWithRequirements := [cursorChannel.toRaw,HostHintQueue.stateChannel.toRaw]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  soundness := by
    circuit_proof_start [openMain,Open.Valid,ClockParts.circuit,ClockOrder.circuit,Gadgets.Equality.circuit,
      queueEffectChannel,HostHintQueue.stateChannel,cursorChannel,Open.order,ClockParts.high24,ClockParts.low24,ClockParts.address]
    obtain ⟨direct,time,eq,order⟩ := h_holds
    exact ⟨direct,time,eq,order⟩
  completeness := by
    circuit_proof_start [openMain,Open.Valid,ClockParts.circuit,ClockOrder.circuit,Gadgets.Equality.circuit,
      queueEffectChannel,HostHintQueue.stateChannel,cursorChannel,Open.order,ClockParts.high24,ClockParts.low24,ClockParts.address]
    obtain ⟨direct,time,eq,order⟩ := h_assumptions
    exact ⟨direct,time,eq,order⟩

/-- One fresh persistent identity and an exact decrease in the number of outstanding buffers. -/
def Step.Valid (r : Step (ZMod p)) : Prop :=
  IsBool r.direct ∧ HintNodeAllocate.Spec r.node ∧ r.node.node.length[3] = 0 ∧
    AddressSum.Spec ⟨r.index,#v[1,0,0],r.remaining⟩

/-- Step the private cursor, publish metadata for the fresh identity and authorize its contents. -/
def stepMain (r : Var Step (ZMod p)) : Circuit (ZMod p) Unit := do
  assertBool r.direct
  let _ ← HintNodeAllocate.circuit r.node
  assertZero r.node.node.length[3]
  assertion AddressSum.circuit ⟨r.index,#v[1,0,0],r.remaining⟩
  cursorChannel.pull r.before
  recordChannel.pullIf (1-r.direct) r.metadata
  HostHintQueue.nodeChannel.emit r.readers r.node.node
  contentsChannel.push r.contents
  cursorChannel.push r.after

instance stepElaborated : ElaboratedCircuit (ZMod p) Step unit stepMain := by elaborate_circuit

/-- A physical node step must implement the certified prepend and the exact remaining count. -/
def stepCircuit : GeneralFormalCircuit (ZMod p) Step unit where
  name := "sp1.native.hint_allocation_node"
  main := stepMain
  elaborated := stepElaborated
  channelsWithRequirements := [recordChannel.toRaw,HostHintQueue.nodeChannel.toRaw,contentsChannel.toRaw,cursorChannel.toRaw]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  soundness := by
    circuit_proof_start [stepMain,Step.Valid,HintNodeAllocate.circuit,AddressSum.circuit,recordChannel,
      HostHintQueue.nodeChannel,cursorChannel,contentsChannel]
    obtain ⟨direct,node,high,remaining⟩ := h_holds
    exact ⟨⟨direct,node.1,high,remaining⟩,by rcases direct with h|h <;> simp [h],fun _ => node.1.2.2.2.2.1⟩
  completeness := by
    circuit_proof_start [stepMain,Step.Valid,HintNodeAllocate.circuit,AddressSum.circuit,recordChannel,
      HostHintQueue.nodeChannel,cursorChannel,contentsChannel]
    obtain ⟨direct,node,high,remaining⟩ := h_assumptions
    exact ⟨direct,node,high,remaining⟩

end SP1Clean.WriteAllocation
