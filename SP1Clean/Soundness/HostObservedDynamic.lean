import SP1Clean.Soundness.HostObservedHistory
import SP1Clean.Soundness.HostObservedProducers
import SP1Clean.Soundness.HostObservedRetirement
import SP1Clean.Soundness.OrdinaryObservationProjection
import SP1Clean.FormalModel.ShardDynamic

/-! # The complete Sail bookkeeping of the physically grounded trace

A chronological CPU walk and the actual observation tape have identical ordinary receipts.
Their common order identifies the last ordinary successor, even if host calls follow it.
Together with the terminal counter this binds all five dynamic target fields.
-/

namespace SP1Clean.Soundness.HostObserved

open Circuit Air.Flat Semantics Channels NativeCore Machine
open SP1Clean.OrdinaryObservation (Inputs State Mode TerminalInputs startFor finalFor)
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

private theorem OrderedHistory.dynamicMatch {header : SP1PublicIO (ZMod p)} {events : List ExecutionEvent}
    {inventory : List (Inputs (ZMod p))} {stored : List (Mode × TerminalInputs (ZMod p))}
    (history : OrderedHistory source.sail target.sail inventory stored)
    (valid : ExecutionSourceValid image source) (boundary : SailBoundary.Spec source target header)
    (lengthEq : events.countP ExecutionEvent.isOrdinary = history.path.length)
    (pc : nextPcAfter events (source.sail.registers.get? Register.nextPC) (some target.pc) =
      (history.path.map (fun input : Inputs (ZMod p) => input.receipt)).foldl (fun _ m => some (StateMsg.pcBits m)) (source.sail.registers.get? Register.nextPC))
    (bounds : ∀ row ∈ history.path, row.receipt.pc1.val < 65536 ∧ row.receipt.pc2.val < 65536) :
    FormalModel.Shard.DynamicMatch source target events := by
  have observations := OrdinaryObservation.terminal_retirement_entries boundary.retirementModes history.valid
  have zero : (history.terminal.previous.clkHigh = 0 ∧ history.terminal.previous.clkLow = 0) ↔
      events.countP ExecutionEvent.isOrdinary = 0 := history.zero_iff.trans (by rw [lengthEq])
  simp only [zero] at observations
  have count := retirement_of_counter valid boundary
    (congrArg SP1Clean.OrdinaryObservation.State.counter history.output) history.counter
  rw [← lengthEq] at count
  exact ⟨(history.nextPC boundary.retirementModes bounds).trans pc.symm, observations.1, count,
    observations.2.1, observations.2.2⟩

private theorem receipt_bounds {witness : EnsembleWitness (LocalCore.ensemble (p := p) image source)}
    (constraints : witness.Constraints) (ordering : LocalCore.OrderingChannels witness)
    (message : StateMsg (ZMod p)) (member : message ∈ (LocalCore.activeInstructionRows witness).map
      (fun r => statePushMessage (r.toChipRow witness.data))) :
    message.pc1.val < 65536 ∧ message.pc2.val < 65536 := by
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  have inCPU : ExecutionRow.instruction row ∈ LocalCore.executionRows witness := by
    simp only [LocalCore.executionRows, List.mem_append]
    exact Or.inl (Or.inl (List.mem_map_of_mem present))
  have bounds := (LocalCore.executionRows_good_of_orderingChannels witness constraints ordering inCPU).2
  exact bounds.2

attribute [local irreducible] ensemble HostFinalMemory.ensemble HostLocalCore.localWitness in
/-- The complete accepted observation ledger binds all five dynamic registers to the same
physical State walk whose labels form the replayed Sail/host tape. -/
theorem dynamicMatch (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (funded : DeclarationsOpen witness) {events : List ExecutionEvent}
    (grounded : HostFinalMemory.PhysicalEventOrder (baseWitness witness) events) : FormalModel.Shard.DynamicMatch source target events := by
  let memory := baseWitness witness
  let projected := HostFinalMemory.baseWitness memory
  let host := HostHintQueueBoundary.projected projected
  let core := HostFinalMemory.coreWitness memory
  have memoryChecked := baseWitness_constraints witness checked
  have projectedChecked := HostFinalMemory.baseWitness_constraints memory memoryChecked
  have hostChecks := HostHintQueueBoundary.projected_constraints projected projectedChecked
  have constraints : core.Constraints := HostLocalCore.localWitness_constraints host hostChecks
  have channels : LocalCore.OrderingChannels core := HostHintQueueBoundary.projected_orderingChannels projected
    (GroundingResources.sourceInterface source.host.io.hints (FinalMemoryChecks.checkTables target.sail.memorySnapshot)) projectedChecked
    (HostFinalMemory.baseWitness_hostBalanced memory (grounding_balance witness funded))
  have contract := LocalCore.public_contract_of_byte core channels.sourceChecks channels.verifierByte
  have sail := target_spec witness funded
  obtain ⟨history⟩ := ordered_history witness checked funded
  change HostHintReadCPU.PhysicalEventOrder projected.data projected.publicInput (LocalCore.executionRows core) events at grounded
  obtain ⟨cpu, exactRows, walk, tape⟩ := grounded
  have edge : ExecutionRow.canonEdge core.data = ExecutionRow.canonEdge projected.data :=
    funext fun row => row.canonEdge_setData _ _
  have lowerHeader : core.publicInput = projected.publicInput := (HostLocalCore.localWitness_publicInput host).trans
    (HostHintQueueBoundary.projected_publicInput projected)
  have header : core.publicInput = witness.publicInput := lowerHeader.trans
    ((HostFinalMemory.baseWitness_publicInput memory).trans (baseWitness_publicInput witness))
  have localWalk : Walk.IsWalk (ExecutionRow.canonEdge core.data) (initialBoundaryStateMessage core.publicInput)
      (finalBoundaryStateMessage core.publicInput) cpu := by rwa [edge, lowerHeader]
  let messages := history.path.map (fun row : Inputs (ZMod p) => row.receipt)
  have matched := active_receipts witness checked funded (consumer_spec witness checked funded)
  have receipts := history.exhaustive.map (fun input : Inputs (ZMod p) => input.receipt)
  have same : ((LocalCore.activeInstructionRows core).map
      (fun row => statePushMessage (row.toChipRow core.data))).Perm messages := matched.trans receipts.symm
  have sorted : ((history.path.map (fun input : Inputs (ZMod p) => input.receipt)).map OrdinaryObservation.receiptRank).Pairwise (· < ·) := by
    simpa only [List.map_map, Function.comp_def, OrdinaryObservation.receiptRank, Inputs.next, OrdinaryObservation.rank]
      using history.sorted
  have facts := OrdinaryObservation.cpu_agreement core constraints channels exactRows localWalk
    messages same sorted (source.sail.registers.get? Register.nextPC)
  dsimp only [messages] at facts
  rw [tape, List.length_map] at facts
  have endpointPC : StateMsg.pcBits (finalBoundaryStateMessage core.publicInput) = target.pc := by
    rw [header]
    exact SailBoundary.TargetFor.pc sail.ranges.2 sail.2.1
  rw [endpointPC] at facts
  exact history.dynamicMatch contract.2.1 sail facts.1 facts.2 fun row member =>
    receipt_bounds constraints channels row.receipt (same.mem_iff.mpr (List.mem_map_of_mem member))

end SP1Clean.Soundness.HostObserved
