import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.LocalCoreExitEvent
import SP1Clean.Semantics.Execution.ParkedSyscall
import SP1Clean.FormalModel.Contracts.ShardHeader

/-! # The physical Exit ledger determines the segment's public exit code -/

namespace SP1Clean.Soundness.HostFinalMemory
open Circuit Air.Flat Channels Semantics Machine

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance exitClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

attribute [local irreducible] ensemble HostLocalCore.localWitness in
private theorem parked (witness : EnsembleWitness (Installed image source target final))
    (constraints : witness.Constraints) (balanced : ExternallyBalanced witness)
    {events : List ExecutionEvent} (order : PhysicalEventOrder witness events)
    (value : witness.publicInput.exit_code ≠ 0) :
    ∃ call, ExecutionEvent.syscall call ∈ events ∧ call.nextPc = haltPc := by
  let projected := baseWitness witness
  let host := HostHintQueueBoundary.projected projected
  let core := HostLocalCore.localWitness host
  have same : core.publicInput = witness.publicInput :=
    (HostLocalCore.localWitness_publicInput host).trans
      ((HostHintQueueBoundary.projected_publicInput projected).trans (baseWitness_publicInput witness))
  have checked : core.Constraints := HostLocalCore.localWitness_constraints host
    (HostHintQueueBoundary.projected_constraints projected (baseWitness_constraints witness constraints))
  have funded : core.BalancedChannel exitChannel.toRaw :=
    HostHintReadCPU.source_exit_balance projected (baseWitness_hostBalanced witness balanced)
  have nonzero : core.publicInput.exit_code ≠ 0 := by rwa [same]
  obtain ⟨call, present, parked⟩ := LocalCore.parked_of_nonzero_exit core checked funded nonzero
  change HostHintReadCPU.PhysicalEventOrder projected.data projected.publicInput (LocalCore.executionRows core) events at order
  exact ⟨call, order.perm.mem_iff.mpr present, parked⟩

omit [Fact (2 ^ 25 < p)] in
private theorem publicExit_value (field : ZMod p)
    (active : ∀ code, source.host.exitCode = none → target.host.exitCode = some code → code.toNat = field.val)
    (nonzero : field ≠ 0 → source.host.exitCode = none ∧ ∃ code, target.host.exitCode = some code) :
    field.val = ((SP1StateBoundary.haltCode source target).getD 0).toNat := by
  by_cases running : source.host.exitCode = none
  · cases stopped : target.host.exitCode with
    | some code => simpa only [SP1StateBoundary.haltCode, running, ↓reduceIte, stopped, Option.getD_some] using
        (active code running stopped).symm
    | none =>
      have zero : field = 0 := by
        by_contra value
        obtain ⟨_, code, contradiction⟩ := nonzero value
        rw [stopped] at contradiction
        cases contradiction
      simp [SP1StateBoundary.haltCode, running, stopped, zero]
  · have zero : field = 0 := by
      by_contra value
      exact running (nonzero value).1
    simp [SP1StateBoundary.haltCode, running, zero]

/-- The numerical Exit field is zero on every continuing or already stopped segment and
is the actual HALT code on a newly stopped segment, including HALT with code zero. -/
theorem publicExit (witness : EnsembleWitness (Installed image source target final))
    (constraints : witness.Constraints) (balanced : ExternallyBalanced witness)
    {events : List ExecutionEvent} {actual : ExecutionState} (valid : image.Valid)
    (path : ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize events actual) (order : PhysicalEventOrder witness events)
    (status : actual.host.exitCode = target.host.exitCode)
    (active : ∀ code, source.host.exitCode = none → actual.host.exitCode = some code →
      code.toNat = witness.publicInput.exit_code.val) :
    witness.publicInput.exit_code.val = ((SP1StateBoundary.haltCode source target).getD 0).toNat := by
  apply publicExit_value _ (fun code running halted => active code running (status.trans halted))
  intro nonzero
  obtain ⟨call, member, stop⟩ := parked witness constraints balanced order nonzero
  obtain ⟨running, halted⟩ := path.halt_of_parked member stop
  exact ⟨running, _, status.symm.trans halted⟩

end SP1Clean.Soundness.HostFinalMemory
