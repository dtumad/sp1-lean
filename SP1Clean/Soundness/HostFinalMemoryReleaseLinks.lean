import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.InstructionReleaseLinks
import SP1Clean.Soundness.LocalCoreEventUniqueness

/-! # Enabled jump-link bounds on the installed CPU walk

The physical State walk and the memory-grounded replay exhaust the same rows in strictly
increasing clock order. Consequently every ordinary replay cut has the authenticated decode
and jump-link guarantee of its actual row, including cuts separated by host calls.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Semantics NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance releaseClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance releaseLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

attribute [local irreducible] ensemble HostLocalCore.localWitness in
/-- Every ordinary cut in this physical event order satisfies the released JAL/JALR link check.
The row and decoder evidence are supplied by grounding the installed CPU and memory ledger. -/
theorem PhysicalEventOrder.releaseLinks (witness : EnsembleWitness (Installed image source target final))
    (valid : image.Valid) (checked : witness.Constraints) (funded : ExternallyBalanced witness)
    {events : List Machine.ExecutionEvent} (order : PhysicalEventOrder witness events) :
    ExecutionPath.ReleaseLinks ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) source.realize events := by
  let projected := baseWitness witness
  let host := HostHintQueueBoundary.projected projected
  let core := HostLocalCore.localWitness host
  have lowerChecked := baseWitness_constraints witness checked
  have lowerFunded := baseWitness_hostBalanced witness funded
  have coreChecked : core.Constraints := HostLocalCore.localWitness_constraints host
    (HostHintQueueBoundary.projected_constraints projected lowerChecked)
  have channels : LocalCore.OrderingChannels core := HostHintQueueBoundary.SourceWitness.orderingChannels projected lowerChecked lowerFunded
  obtain ⟨carrier⟩ := HostHintReadCPU.source_grounding_carrier valid projected lowerChecked lowerFunded
  change HostHintReadCPU.PhysicalEventOrder projected.data projected.publicInput (LocalCore.executionRows core) events at order
  obtain ⟨ordered, exhaust, walk, rfl⟩ := order
  have sorted (rows : List (ExecutionRow p)) (inventory : rows.Perm (LocalCore.executionRows core))
      (cpu : Walk.IsWalk (ExecutionRow.canonEdge projected.data) (initialBoundaryStateMessage projected.publicInput)
        (finalBoundaryStateMessage projected.publicInput) rows) :
      (rows.map fun row => StateMsg.timeNat (row.edge core.data).1).Pairwise (· < ·) := by
    apply LocalCore.ordered_times_pairwise core coreChecked channels inventory
    have edge : ExecutionRow.canonEdge core.data = ExecutionRow.canonEdge projected.data := funext fun row => row.canonEdge_setData _ _
    have header : core.publicInput = projected.publicInput :=
      (HostLocalCore.localWitness_publicInput host).trans (HostHintQueueBoundary.projected_publicInput projected)
    rwa [edge, header]
  have same : ordered = carrier.ordered := by
    apply (exhaust.trans carrier.exhaustive.symm).eq_of_pairwise (le := fun a b =>
      StateMsg.timeNat (a.edge core.data).1 < StateMsg.timeNat (b.edge core.data).1)
    · exact fun _ _ _ _ lt gt => (Nat.lt_asymm lt gt).elim
    · exact List.pairwise_map.mp (sorted ordered exhaust walk)
    · exact List.pairwise_map.mp (sorted carrier.ordered carrier.exhaustive carrier.cpuWalk)
  rw [same]
  change ExecutionPath.ReleaseLinks _ _ _ carrier.events
  intro cut current ordinary prefixReplay
  simp only [ExecutionCarrier.events, List.getElem?_map] at ordinary
  obtain ⟨row, atRow, label⟩ := Option.map_eq_some_iff.mp ordinary
  cases row with
  | instruction row =>
    obtain ⟨_, _, _, _, fixed, dynamic, active, decoded, atPc, configured⟩ :=
      carrier.instruction_step_at valid lowerChecked lowerFunded atRow prefixReplay
    exact row.releaseLinkAt fixed dynamic active decoded atPc configured
  | halt row => cases label
  | syscall row => cases label

end SP1Clean.Soundness.HostFinalMemory
