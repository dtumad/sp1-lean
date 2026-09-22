import SP1Clean.Soundness.HostHintReadExecutionPath

/-! # Protected instruction memory throughout the installed mixed replay

Every replayed prefix preserves the incoming protected bytes. Ordinary instructions obtain
write permission from the actual AIR ledger; host steps use the same byte policy through their
semantic interpreter. The checked incoming boundary therefore supplies ROM contents at every
prefix, including empty and host-only segments, without a caller-supplied ROM invariant.

This theorem concerns the installed instruction/control/hint ensemble. It does not impose an
ordinary write policy or resource bounds on the independent `ExecutionPath` relation.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance romLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance romLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem readOnly_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (n : ℕ) (current next : ExecutionState) (event : Machine.ExecutionEvent)
    (atEvent : carrier.events[n]? = some event)
    (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize (carrier.events.take n) = some current)
    (replay : replayStep? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      current event = some next) (address : ℕ) (readOnly : image.readOnly address = true) :
    next.sail.mem.get? address = current.sail.mem.get? address := by
  simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
  obtain ⟨row, atRow, rfl⟩ := Option.map_eq_some_iff.mp atEvent
  have member := carrier.exhaustive.mem_iff.mp (List.mem_of_getElem? atRow)
  cases row with
  | instruction row =>
    obtain ⟨_, effect⟩ := carrier.instruction_effect_at valid constraints balanced atRow prefixReplay replay
    have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) ∧
        (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data).is_real = 1 := by
      simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
    have permission := HostLocalCore.instructionRows_write_permitted (HostHintQueueBoundary.expanded witness)
      (auxiliary_permission_pulls (HostQueueCurrent.source_permission_pulls source final bankFinal))
      (HostHintQueueBoundary.expanded_constraints witness constraints)
      (HostHintQueueBoundary.expanded_balanced witness balanced) active.1 active.2
    have dataEq : (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data = witness.data := rfl
    rw [dataEq] at permission
    exact effect.readOnly_of_writePermission permission address readOnly
  | syscall row | halt row =>
    exact (hostStep_effect ((replayHost?_eq_some_iff _ _ _ _ _).mp replay)).2.2.2 address readOnly

/-- Every successful prefix of the installed replay preserves each protected byte exactly. -/
theorem GroundingCarrier.readOnly_prefix (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cut : ℕ} {target : ExecutionState}
    (replay : carrier.pairedTrajectory valid cut = some target)
    (address : ℕ) (readOnly : image.readOnly address = true) :
    target.sail.mem.get? address = source.sail.realize.mem.get? address := by
  apply replayEvents?_preserves (fun state => state.sail.mem.get? address) replay
  intro n current next event atEvent prefixReplay step
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atEvent
  simp only [List.length_take] at bound
  have before : n < cut := lt_of_lt_of_le bound (Nat.min_le_left _ _)
  rw [List.getElem?_take_of_lt before] at atEvent
  simp only [List.take_take, Nat.min_eq_left before.le] at prefixReplay
  exact readOnly_step valid carrier constraints balanced n current next event atEvent prefixReplay step address readOnly

/-- The incoming boundary's authenticated ROM survives every prefix of the installed replay. -/
theorem GroundingCarrier.romLoaded_prefix (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cut : ℕ} {target : ExecutionState}
    (replay : carrier.pairedTrajectory valid cut = some target) :
    Target.RomLoaded (image.toGuestProgram valid) target.sail := by
  have checked := HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.expanded_constraints witness constraints)
  have ordering := HostLocalCore.orderingChannels (HostHintQueueBoundary.expanded witness)
    (auxiliaryInterface (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints)))
    (HostHintQueueBoundary.expanded_constraints witness constraints)
    (HostHintQueueBoundary.expanded_balanced witness balanced)
  have contract := LocalCore.public_contract_of_byte _ checked (ordering.byte _ (HostLocalCore.localWitness
    (HostHintQueueBoundary.expanded witness)).mem_allTables_verifierTable)
  exact romLoaded_of_readOnly image valid (carrier.readOnly_prefix valid constraints balanced replay) contract.2.1.romLoaded

end SP1Clean.Soundness.HostHintReadCPU
