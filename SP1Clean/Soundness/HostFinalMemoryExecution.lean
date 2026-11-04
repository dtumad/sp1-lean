import SP1Clean.Soundness.HostFinalMemorySoundness
import SP1Clean.Soundness.HostHintReadFinalSnapshot
import SP1Clean.Soundness.HostCommitDeclarations

/-! # Execution of the complete-memory host assembly

The balance premise `DeclarationsOpen` covers every channel except the commitment declarations,
whose verifier-owned provider is installed above this assembly. The Memory proof view retains
every physical table, including the target validators, and balances every channel except those
declarations and the three final-memory receipt channels (`HostHintQueueBoundary.hiddenChannels`).
That is exactly what the host grounding proofs read, so raw acceptance of the complete assembly
yields their local execution path. The installed finite target comparison and the path's own
final-record characterization read the same physical finalizer rows; together they identify every
integer register and the entire Sail RAM map of the path's final state with the supplied outgoing
snapshot. Each commitment call of the path also requests its declaration in the witness ledger
(`CommitmentEnsemble.Declared`). Complete outgoing Sail/host equality remains separate.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core Semantics
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance executionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance executionClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {outgoing : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}

/-- The installed complete-memory assembly with the concrete six-call host registry. -/
abbrev Installed (image : ProgramImage) (source : ExecutionSnapshot) (outgoing : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) :=
  ensemble image source outgoing final bankFinal HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) (sourceChannels outgoing)
    (source_unique_names image source outgoing) (source_registration image source outgoing)

/-- Balance on every registered channel except commitment declarations. The verifier-owned
statement provider that supplies them is installed above this assembly. -/
def DeclarationsOpen (witness : EnsembleWitness (Installed image source outgoing final bankFinal)) : Prop :=
  ∀ channel ∈ (Installed image source outgoing final bankFinal).channels,
    channel ≠ CommitmentDeclaration.channel.toRaw → witness.BalancedChannel channel

/-- Complete balance in particular balances everything but the declarations. -/
theorem DeclarationsOpen.of_balancedChannels
    {witness : EnsembleWitness (Installed image source outgoing final bankFinal)}
    (balanced : witness.BalancedChannels) : DeclarationsOpen witness :=
  fun channel member _ => balanced channel member

/-- The Memory proof view balances every channel the host proofs read. -/
theorem baseWitness_hostBalanced (witness : EnsembleWitness (Installed image source outgoing final bankFinal))
    (balanced : DeclarationsOpen witness) : HostHintQueueBoundary.Balanced (baseWitness witness) := by
  intro channel registered visible
  have receipt (ram : Bool) : channel ≠ (FinalMemoryValue.channel ram).toRaw := by
    rintro rfl
    exact visible (by cases ram <;> simp [HostHintQueueBoundary.hiddenChannels])
  apply baseWitness_balancedChannel witness channel registered (receipt false) (receipt true)
    (by rintro rfl; exact visible (by simp [HostHintQueueBoundary.hiddenChannels]))
  apply balanced
  · exact List.mem_append_left _ registered
  · rintro rfl
    exact visible (by simp [HostHintQueueBoundary.hiddenChannels])

/-- The installed target comparison needs Byte closure and its private Memory channels only. -/
theorem checkFinal_of_declarationsOpen
    (witness : EnsembleWitness (Installed image source outgoing final bankFinal))
    (checked : witness.Constraints) (balanced : DeclarationsOpen witness) :
    source.sail.memorySnapshot.checkFinal outgoing
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness (source_privacy outgoing source.host.io.hints) checked
    (byte_guarantees witness (HostHintReadLocal.source_interface source.host.io.hints) checked
      (balanced _ ?_ (by simp [CommitmentDeclaration.channel, Channels.byteChannel, Channel.toRaw])))
  · intro channel member
    apply balanced
    · apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      obtain ⟨component, present, used⟩ := List.mem_flatMap.mp (check_channels channel member)
      exact (source_registration image source outgoing).tables component
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ present))) used
    · simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [CommitmentDeclaration.channel, FinalMemoryValue.channel, FinalMemoryChange.channel,
          FinalRegisterValue.membership, InitialMemoryLookup.membership, StaticTable.channel, Channel.toRaw]
  · apply List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    simp [HostLocalCore.baseEnsemble, HostLocalCore.registry, LocalCore.baseEnsemble, sp1Ensemble_channels]

/-- **Complete-memory execution.** Constraints and balance outside the commitment declarations
yield one local RISC-V/host path from the complete source. Its final integer registers and entire RAM map are the
supplied outgoing snapshot; the remaining endpoint observations are those of the host proofs. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (Installed image source outgoing final bankFinal))
    (constraints : witness.Constraints) (balanced : DeclarationsOpen witness) :
    ∃ events target hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ index, target.sail.get_reg? index = some (outgoing.read (.reg index))) ∧
      target.sail.mem = outgoing.memory.toSailMemory (2 ^ 48) ∧
      (target.sail.cycleCount = source.sail.cycleCount ∧ target.sail.sailOutput = source.sail.output) ∧
      target.sail.regs.get? Register.nextPC = nextPcAfter events
        (source.sail.registers.get? Register.nextPC)
        (some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput))) ∧
      (target.sail.regs.get? Register.minstret_increment =
        (if events.countP Machine.ExecutionEvent.isOrdinary = 0
          then source.sail.registers.get? Register.minstret_increment
          else some (retirementEnabled source.sail.realize)) ∧
        target.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
          (fun value => value + BitVec.ofNat 64
            (if retirementEnabled source.sail.realize then events.countP Machine.ExecutionEvent.isOrdinary else 0))) ∧
      (∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
        R ≠ Register.minstret_increment → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
          target.sail.regs.get? R = source.sail.registers.get? R) ∧
      HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      target.host = { source.host with
        io.hints := hints
        committed := bankFinal.committed
        deferred := bankFinal.deferred
        exitCode := bankFinal.exitCode } ∧
      (∀ code : BitVec 32, source.host.exitCode = none → target.host.exitCode = some code →
        code.toNat = witness.publicInput.exit_code.val) ∧
      CommitmentEnsemble.Declared witness events := by
  have checked := checkFinal_of_declarationsOpen witness constraints balanced
  have baseConstraints := baseWitness_constraints witness constraints
  have baseBalanced := baseWitness_hostBalanced witness balanced
  obtain ⟨events, target, hints, path, permitted, inventory, clock, pc, -, -, runtime, nextPC, retirement,
    preserved, decoded, host, exit, memory⟩ :=
    HostHintReadCPU.source_execution_with_memory valid (baseWitness witness) baseConstraints baseBalanced
  rw [finalRecords_eq_core] at checked
  obtain ⟨registers, ram⟩ := (memory outgoing).mp checked
  rw [baseWitness_publicInput] at clock pc nextPC exit
  have declared := (HostCommitDeclarations.rows_declared valid (baseWitness witness) baseConstraints
    baseBalanced).of_perm inventory
  refine ⟨events, target, hints, path, permitted, clock, pc, registers, ram, runtime, nextPC, retirement,
    preserved, decoded, host, exit, declared.transfer fun interaction member => ?_⟩
  rw [baseWitness_interactions witness _ (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel,
    Channel.toRaw]) (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel, Channel.toRaw])] at member
  exact ClosedVerifier.mem_interactionsWith_of_project _ witness member

end SP1Clean.Soundness.HostFinalMemory
