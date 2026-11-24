import SP1Clean.Soundness.HostQueueCallProjection

/-! # Actual host-call classification with the shared ENTER/VERIFY receipt

The source, terminal host and complete target validators determine the physical host inventory.
The profile changes one receiver at its existing position. This projection authenticates call
codes and dispatch from instruction handoffs; whole-execution replay for the extended profile
also needs memory, commitment and exit agreement.
-/

namespace SP1Clean.Soundness.HostRegisteredCalls

open Circuit Air.Flat Semantics HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
attribute [local instance] FiniteField.instDecidableEq

/-- The complete host boundary and target-validator registration for the selected no-effect slot. -/
abbrev ensemble (includeVerify : Bool) (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) : Ensemble (ZMod p) SP1PublicIO :=
  let registration := HostFinalMemory.source_registration (p := p) image source target.sail.memorySnapshot includeVerify
  HostHintQueueBoundary.ensemble image source final target.host (HostCallReceivers.availableFor includeVerify)
    (sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables target.sail.memorySnapshot)
    (HostFinalMemory.sourceChannels target.sail.memorySnapshot)
    (HostFinalMemory.source_unique_names image source target.sail.memorySnapshot includeVerify)
    registration.unique registration.tables registration.boundary

variable {includeVerify : Bool} {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}

private def noopIndex (includeVerify : Bool) :
    Fin (HostHintReadHandoff.receiver (p := p) :: HostCallReceivers.availableFor includeVerify).length :=
  ⟨2, by change 2 < 21; decide⟩

/-- Both profiles place their no-effect calls in the third physical receiver, after HINT_READ and HALT. -/
def noopTable (witness : EnsembleWitness (ensemble includeVerify image source target final)) : Table (ZMod p) :=
  HostLocalHandoff.receiverTable (HostHintQueueBoundary.projected witness) (noopIndex (p := p) includeVerify)

/-- The selected physical slot has the registered component, including the shared circuit in the seven-call profile. -/
theorem noopTable_component (witness : EnsembleWitness (ensemble includeVerify image source target final)) :
    (noopTable witness).component = (HostCallReceivers.profileNoop includeVerify).component :=
  HostLocalHandoff.receiverTable_component (HostHintQueueBoundary.projected witness) (noopIndex (p := p) includeVerify)

/-- Every physical receipt counts once and has a distinct instruction clock. This slot has no padding rows. -/
theorem receipt_heights (witness : EnsembleWitness (ensemble includeVerify image source target final))
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) :
    let receipts := ReceiverView.tableMessages (HostCallReceivers.profileNoop includeVerify) (noopTable witness)
    receipts.length = (noopTable witness).table.length ∧ (receipts.map HostCallLedger.clock).Nodup := by
  let physical := HostHintQueueBoundary.projected witness
  have interface := GroundingResources.sourceInterface (p := p) source.host.io.hints
    (FinalMemoryChecks.checkTables target.sail.memorySnapshot) includeVerify
  refine ⟨?_, ?_⟩
  · have active : (HostCallReceivers.profileNoop (p := p) includeVerify).activity = .const 1 := by
      cases includeVerify <;> rfl
    simp [ReceiverView.tableMessages, active, Expression.eval]
  · exact HostLocalHandoff.receiver_clocks_nodup_of_orderingChannels physical (resources_hostCall_silent interface)
      (HostHintQueueBoundary.projected_constraints witness constraints)
      (HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced)
      (HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced) _ (noopIndex (p := p) includeVerify).isLt

/-- Every actual instruction-produced call has an admitted full code and either its physical
queue row or a successful complete control dispatch with the authenticated result and no RAM write. -/
theorem classified (witness : EnsembleWitness (ensemble includeVerify image source target final))
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness)
    (message : HostCallChip.Message (ZMod p))
    (member : message ∈ HostCallLedger.calls (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness))
      (HostHintQueueBoundary.projected witness).data) :
    HostReceiptProfile.code includeVerify (Word.toBitVec64 message.code) ∧
    ((∃ row ∈ HostQueueOrder.activeRows (queueTables (HostHintQueueBoundary.projected witness)),
        message = HostQueueCPUOrder.call row) ∨
      (Word.toBitVec64 message.code ≠ SyscallKind.hintRead.code ∧
        ∀ (host : HostState), host.exitCode = none → ∀ (policy : HostPolicy), policy.characteristic = p →
        ∀ (context : HostReadContext),
          (context.register 5 = some (Word.toBitVec64 message.code) ∧
            context.register 10 = some (Word.toBitVec64 message.arg1) ∧
            context.register 11 = some (Word.toBitVec64 message.arg2)) →
          ∃ execution, host.run policy context = some execution ∧
            execution.result = Word.toBitVec64 message.result ∧ execution.effect.write = none)) := by
  let physical := HostHintQueueBoundary.projected witness
  let checks := FinalMemoryChecks.checkTables (p := p) target.sail.memorySnapshot
  have interface := GroundingResources.sourceInterface source.host.io.hints checks includeVerify
  have checked := HostHintQueueBoundary.projected_constraints witness constraints
  have records := HostHintQueueBoundary.record_channels witness balanced
  have calls := HostLocalHandoff.calls_perm_of_balancedChannel physical (resources_hostCall_silent interface)
    checked (HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced)
  have received := calls.mem_iff.mp member
  have authentication := source_record_authentication (includeVerify := includeVerify) physical
    (fun component added => ⟨GroundingResources.silent (extra := checks) (channel := HostHintQueue.nodeChannel.toRaw)
        (by simp [groundingChannels]) component added,
      GroundingResources.silent (extra := checks) (channel := HostHintQueue.wordChannel.toRaw)
        (by simp [groundingChannels]) component added⟩)
    _ (.refl _) checked
  exact ⟨HostQueueCallProjection.calls_code physical interface checked records.byte
      (queue_specs physical interface _ authentication checked records) message received,
    HostQueueCallProjection.calls_run_or_queue physical interface checked records.byte message received⟩

end SP1Clean.Soundness.HostRegisteredCalls
