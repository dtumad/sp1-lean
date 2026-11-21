import SP1Clean.Soundness.HostFinalMemorySoundness
import SP1Clean.Soundness.HostHintReadFinalSnapshot
import SP1Clean.Soundness.HostCommitDeclarations

/-! # Execution of the complete-memory host assembly

The host projection uses balance away from commitment declarations, instruction receipts and
observation state. The commitment provider, receipt-bearing instructions and verifier observation
endpoints supply those channels in the outer assembly. The final-memory proof checks its own
three receipt protocols before projecting to the host. The installed finite target comparison
and the path's own final-record characterization read the same physical finalizer rows; together they identify every
integer register and the entire Sail RAM map of the path's final state with the supplied outgoing
snapshot. Each commitment call of the path also requests its declaration in the witness ledger
(`CommitmentEnsemble.Declared`). Complete outgoing Sail/host equality remains separate.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Semantics
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance executionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance executionClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}

/-- The installed complete-memory assembly with the concrete six-call host registry, for a supplied
source and target snapshot. The target fixes the outgoing memory snapshot and the final host
bank. -/
abbrev Installed (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) :=
  ensemble image source target.sail.memorySnapshot final target.host HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) (sourceChannels target.sail.memorySnapshot)
    (source_unique_names image source target.sail.memorySnapshot)
    (source_registration image source target.sail.memorySnapshot)

/-- Channels supplied above the complete-memory host proof view. -/
def externalChannels : List (RawChannel (ZMod p)) :=
  [CommitmentDeclaration.channel.toRaw, InstructionReceipt.channel.toRaw, OrdinaryObservation.stateChannel.toRaw]

/-- The host and memory proofs consume all except the declaration and ordinary observation protocols. -/
def ExternallyBalanced (witness : EnsembleWitness (Installed image source target final)) : Prop :=
  ∀ channel ∈ (Installed image source target final).channels,
    channel ∉ externalChannels (p := p) → witness.BalancedChannel channel

/-- Complete balance restricts to all channels consumed by the host and memory proofs. -/
theorem ExternallyBalanced.of_balancedChannels
    {witness : EnsembleWitness (Installed image source target final)}
    (balanced : witness.BalancedChannels) : ExternallyBalanced witness :=
  fun channel member _ => balanced channel member

/-- The Memory proof view balances every channel the host proofs read. -/
theorem baseWitness_hostBalanced (witness : EnsembleWitness (Installed image source target final))
    (balanced : ExternallyBalanced witness) : HostHintQueueBoundary.Balanced (baseWitness witness) := by
  intro channel registered visible
  have receipt (ram : Bool) : channel ≠ (FinalMemoryValue.channel ram).toRaw := by
    rintro rfl
    exact visible (by cases ram <;> simp [HostHintQueueBoundary.hiddenChannels])
  apply baseWitness_balancedChannel witness channel registered (receipt false) (receipt true)
    (by rintro rfl; exact visible (by simp [HostHintQueueBoundary.hiddenChannels]))
  apply balanced
  · exact List.mem_append_left _ registered
  · intro external
    apply visible
    change channel ∈ _ :: _ :: _ :: externalChannels
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ external))

/-- The installed target comparison needs Byte closure and its private Memory channels only. -/
theorem checkFinal_of_externalBalance
    (witness : EnsembleWitness (Installed image source target final))
    (checked : witness.Constraints) (balanced : ExternallyBalanced witness) :
    source.sail.memorySnapshot.checkFinal target.sail.memorySnapshot
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness (source_privacy target.sail.memorySnapshot source.host.io.hints) checked
    (byte_guarantees witness (HostHintReadLocal.source_interface source.host.io.hints) checked
      (balanced _ ?_ (by simp [externalChannels, CommitmentDeclaration.channel, InstructionReceipt.channel,
        OrdinaryObservation.stateChannel, Channels.byteChannel, Channel.toRaw])))
  · intro channel member
    apply balanced
    · apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      obtain ⟨component, present, used⟩ := List.mem_flatMap.mp (check_channels channel member)
      exact (source_registration image source target.sail.memorySnapshot).tables component
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ present))) used
    · simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [externalChannels, CommitmentDeclaration.channel, InstructionReceipt.channel,
          OrdinaryObservation.stateChannel, FinalMemoryValue.channel, FinalMemoryChange.channel,
          FinalRegisterValue.membership, InitialMemoryLookup.membership, StaticTable.channel, Channel.toRaw]
  · apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    simp [HostLocalCore.baseEnsemble, HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels]

/-- The grounded CPU row order, retained across the host, final-memory and verifier projections. -/
def PhysicalEventOrder (witness : EnsembleWitness (Installed image source target final))
    (events : List Machine.ExecutionEvent) : Prop :=
  let projected := baseWitness witness
  HostHintReadCPU.PhysicalEventOrder projected.data projected.publicInput
    (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected projected))) events

/-- **Complete-memory execution.** Constraints and balance outside the commitment declarations
yield one local RISC-V/host path from the complete source. Its final integer registers and entire RAM map are the
supplied outgoing snapshot; the remaining endpoint observations are those of the host proofs. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (Installed image source target final))
    (constraints : witness.Constraints) (balanced : ExternallyBalanced witness) :
    ∃ events actual hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events actual ∧
      actual.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      actual.sail.regs.get? Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ index, actual.sail.get_reg? index = some (target.sail.memorySnapshot.read (.reg index))) ∧
      actual.sail.mem = target.sail.memorySnapshot.memory.toSailMemory (2 ^ 48) ∧
      (actual.sail.cycleCount = source.sail.cycleCount ∧ actual.sail.sailOutput = source.sail.output) ∧
      actual.sail.regs.get? Register.nextPC = nextPcAfter events
        (source.sail.registers.get? Register.nextPC)
        (some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput))) ∧
      (actual.sail.regs.get? Register.minstret_increment =
        (if events.countP Machine.ExecutionEvent.isOrdinary = 0
          then source.sail.registers.get? Register.minstret_increment
          else some (retirementEnabled source.sail.realize)) ∧
        actual.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
          (fun value => value + BitVec.ofNat 64
            (if retirementEnabled source.sail.realize then events.countP Machine.ExecutionEvent.isOrdinary else 0))) ∧
      (actual.sail.regs.get? Register.mip =
        (if events.countP Machine.ExecutionEvent.isOrdinary = 0 then source.sail.registers.get? Register.mip
          else some (TryStepReduction.refreshedMip source.sail.realize)) ∧
        actual.sail.regs.get? Register.written_event_index =
          (if events.countP Machine.ExecutionEvent.isOrdinary = 0
            then source.sail.registers.get? Register.written_event_index else some none)) ∧
      (∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
        R ≠ Register.minstret_increment → R ≠ Register.mip → R ≠ Register.written_event_index → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
          actual.sail.regs.get? R = source.sail.registers.get? R) ∧
      HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      actual.host = { source.host with
        io.hints := hints
        committed := target.host.committed
        deferred := target.host.deferred
        exitCode := target.host.exitCode } ∧
      (∀ code : BitVec 32, source.host.exitCode = none → actual.host.exitCode = some code →
        code.toNat = witness.publicInput.exit_code.val) ∧
      (∀ event ∈ events, SixCallProfile.event event) ∧ PhysicalEventOrder witness events ∧
      CommitmentEnsemble.Declared witness events := by
  have checked := checkFinal_of_externalBalance witness constraints balanced
  have baseConstraints := baseWitness_constraints witness constraints
  have baseBalanced := baseWitness_hostBalanced witness balanced
  obtain ⟨events, actual, hints, path, inventory, clock, pc, -, -, runtime, nextPC, retirement, platform,
    preserved, decoded, host, exit, memory⟩ :=
    HostHintReadCPU.source_execution_with_memory valid (baseWitness witness) baseConstraints baseBalanced
  rw [finalRecords_eq_core] at checked
  obtain ⟨registers, ram⟩ := (memory target.sail.memorySnapshot).mp checked
  rw [baseWitness_publicInput] at clock pc nextPC exit
  have declared := (HostCommitDeclarations.rows_declared valid (baseWitness witness) baseConstraints
    baseBalanced).of_perm inventory.perm
  refine ⟨events, actual, hints, path, clock, pc, registers, ram, runtime, nextPC, retirement, platform,
    preserved, decoded, host, exit,
    fun event member => HostHintReadCPU.installed_events (baseWitness witness) baseConstraints baseBalanced event
      (inventory.perm.mem_iff.mp member), inventory, declared.transfer fun interaction member => ?_⟩
  rw [baseWitness_interactions witness _ (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel,
    Channel.toRaw]) (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel, Channel.toRaw])] at member
  exact ClosedVerifier.mem_interactionsWith_of_project _ witness member

end SP1Clean.Soundness.HostFinalMemory
